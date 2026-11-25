-- Prove2me | solution 1 for SimpleGraph.bernoulliProb_isClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:48.036193+00:00
-- url     : https://prove2.me/submissions/6984f844-9f2a-4764-a8f8-c9c737e2aac0

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Theorems.Thm_Finset_pairs_mono
public import Theorems.Thm_Finset_card_pairs
public import Theorems.Thm_Finset_bernoulliProb_superset


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
namespace SimpleGraph
theorem _root_.solution (s : Finset V) :
    (possibleEdges V).bernoulliProb p (s.pairs ⊆ ·) = p ^ (#s).choose 2 := by
  rw [bernoulliProb_superset (show s.pairs ⊆ possibleEdges V from pairs_mono (subset_univ s)),
    card_pairs]
end SimpleGraph
