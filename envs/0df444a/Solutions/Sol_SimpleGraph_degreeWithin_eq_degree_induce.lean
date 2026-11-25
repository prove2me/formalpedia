-- Prove2me | solution 1 for SimpleGraph.degreeWithin_eq_degree_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:07.19226+00:00
-- url     : https://prove2.me/submissions/85c97aee-dc59-425c-9a0b-4cbf8643f0dd

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution {S : Finset V} {v : V} (hv : v ∈ S) :
    G.degreeWithin S v = (G.induce (S : Set V)).degree ⟨v, hv⟩ := by
  rw [degreeWithin, ← card_neighborFinset_eq_degree]
  refine card_bij (fun w hw => ⟨w, (mem_filter.mp hw).1⟩) (fun w hw => ?_) (fun a _ b _ h => ?_)
    fun w hw => ⟨w.1, ?_, rfl⟩
  · simpa using (mem_filter.mp hw).2
  · simpa using congrArg Subtype.val h
  · simpa using hw
end SimpleGraph
