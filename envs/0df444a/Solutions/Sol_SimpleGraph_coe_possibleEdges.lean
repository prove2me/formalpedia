-- Prove2me | solution 1 for SimpleGraph.coe_possibleEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:26.689221+00:00
-- url     : https://prove2.me/submissions/fa37ea5e-0e3b-4062-8b22-f78304f148de

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open SimpleGraph
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution : (possibleEdges V : Set (Sym2 V)) = Sym2.diagSetᶜ := by
  ext e
  induction e using Sym2.ind with
  | _ v w => simp [possibleEdges, Finset.pairs, Sym2.diagSet]
end SimpleGraph
