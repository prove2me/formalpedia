-- Prove2me | solution 1 for SimpleGraph.isClique_compl_fromEdgeSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:38.670866+00:00
-- url     : https://prove2.me/submissions/0bfdd930-3243-494f-aeea-5e238d5cde65

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
public import Theorems.Thm_Finset_mem_pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution {A : Finset (Sym2 V)} {s : Finset V} :
    (fromEdgeSet (A : Set (Sym2 V)))ᶜ.IsClique (s : Set V) ↔ Disjoint s.pairs A := by
  constructor
  · intro h
    refine Finset.disjoint_left.mpr fun e he heA => ?_
    induction e using Sym2.ind with
    | _ v w =>
      obtain ⟨hv, hw, hvw⟩ := mem_pairs.mp he
      exact ((compl_adj _ _ _).mp (h hv hw hvw)).2 ((fromEdgeSet_adj _).mpr ⟨heA, hvw⟩)
  · intro h v hv w hw hvw
    refine (compl_adj _ _ _).mpr ⟨hvw, fun hadj => ?_⟩
    exact Finset.disjoint_left.mp h (mem_pairs.mpr ⟨hv, hw, hvw⟩)
      (by exact_mod_cast ((fromEdgeSet_adj _).mp hadj).1)
end SimpleGraph
