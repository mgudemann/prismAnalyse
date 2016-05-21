# prismAnalyse

Analyses Prism models using the parser of Prism directly. The main goal is to
minimized the size of the MTBDD required to construct the parallel composition,
i.e., the transition matrix.

For this, it is often sensible to look closer at the state variables. Some may
be unused and better be defined as constants, others might have a range that is
too large.

The program also suggests a sequence of state variable that reduces the size of
the MTBDD. Prism currently does not support variable reordering, but uses
directly the ordering specified in the model file. ```prismAnalyse``` uses the
method described in *Generating compact MTBDD-representations from Probmela
specifications* (SPIN'08) by Frank Ciesinski, Christel Baier, Marcus Größer,
David Parker to suggest a better ordering.

## Usage

```$ java -cp $PRISM_DIR/classes:$PRISM_DIR/lib/prism.jar:. PrismAnalyse $PRISM_FILE```
