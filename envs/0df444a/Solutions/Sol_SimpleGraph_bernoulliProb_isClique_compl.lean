-- Prove2me | solution 1 for SimpleGraph.bernoulliProb_isClique_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:00.38161+00:00
-- url     : https://prove2.me/submissions/27eac381-f0ac-484b-8ed3-7ae2bf70aef1

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
public import Theorems.Thm_Finset_bernoulliProb_disjoint


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
namespace SimpleGraph
theorem _root_.solution (s : Finset V) :
    (possibleEdges V).bernoulliProb p (Disjoint · s.pairs) = (1 - p) ^ (#s).choose 2 := by
  rw [bernoulliProb_disjoint (show s.pairs ⊆ possibleEdges V from pairs_mono (subset_univ s)),
    card_pairs]
end SimpleGraph
