-- Prove2me | solution 1 for SimpleGraph.sum_cliqueCountIn_neighbors_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:47:57.445808+00:00
-- url     : https://prove2.me/submissions/302381d4-4ac0-4c76-8994-ece88eb086a6

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_cliqueCountIn_one
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ


attribute [local simp] SimpleGraph.cliqueCountIn_one

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) = j * G.cliqueCountIn S j := by
  set C : Finset (Finset V) := (S.powersetCard j).filter fun T : Finset V => G.IsClique (T : Set V)
    with hC
  have hterm : ∀ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) =
      ∑ T ∈ C, if v ∈ T then 1 else 0 := by
    intro v hv
    rw [← card_filter, cliqueCountIn]
    refine card_bij (fun U _ => insert v U) (fun U hU => ?_) (fun U hU U' hU' h => ?_)
      fun T hT => ?_
    · rw [mem_filter, mem_powersetCard] at hU
      obtain ⟨⟨hUsub, hUcard⟩, hUcl⟩ := hU
      have hvU : v ∉ U := fun h => G.irrefl (mem_filter.mp (hUsub h)).2
      rw [mem_filter, hC, mem_filter, mem_powersetCard]
      refine ⟨⟨⟨insert_subset hv fun x hx => (mem_filter.mp (hUsub hx)).1, ?_⟩, ?_⟩,
        mem_insert_self _ _⟩
      · rw [card_insert_of_notMem hvU, hUcard]; omega
      · rw [coe_insert]
        exact hUcl.insert fun b hb _ => (mem_filter.mp (hUsub hb)).2
    · have hv1 : v ∉ U := fun h' => G.irrefl
        (mem_filter.mp ((mem_powersetCard.mp (mem_filter.mp hU).1).1 h')).2
      have hv2 : v ∉ U' := fun h' => G.irrefl
        (mem_filter.mp ((mem_powersetCard.mp (mem_filter.mp hU').1).1 h')).2
      have h2 := congrArg (fun A => A.erase v) h
      simpa [erase_insert hv1, erase_insert hv2] using h2
    · rw [mem_filter, hC, mem_filter, mem_powersetCard] at hT
      obtain ⟨⟨⟨hTS, hTcard⟩, hTcl⟩, hvT⟩ := hT
      refine ⟨T.erase v, ?_, insert_erase hvT⟩
      rw [mem_filter, mem_powersetCard, card_erase_of_mem hvT, hTcard]
      refine ⟨⟨fun x hx => ?_, rfl⟩, hTcl.subset (by simp)⟩
      obtain ⟨hxv, hxT⟩ := mem_erase.mp hx
      exact mem_filter.mpr ⟨hTS hxT, hTcl hvT hxT (Ne.symm hxv)⟩
  calc ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1)
      = ∑ v ∈ S, ∑ T ∈ C, if v ∈ T then 1 else 0 := sum_congr rfl hterm
    _ = ∑ T ∈ C, ∑ v ∈ S, if v ∈ T then 1 else 0 := sum_comm
    _ = ∑ _T ∈ C, j := by
        refine sum_congr rfl fun T hT => ?_
        have hT' := mem_powersetCard.mp (mem_filter.mp hT).1
        rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr hT'.1, hT'.2]
    _ = j * G.cliqueCountIn S j := by rw [sum_const, smul_eq_mul, mul_comm, hC]; rfl
end SimpleGraph
