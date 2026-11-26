-- Prove2me | solution 1 for P2M_AME125_sum___dot_53c9426ac755
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:03.252793+00:00
-- url     : https://prove2.me/submissions/172e5d09-b737-47a7-a6e6-57cc1af3e28e

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_P2M_AME125___sum_6e85a0b989be
public import Theorems.Thm_P2M_AME125_sum___mul_eee3c500cad9
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {k : ℕ} (e : Fin k → ZMod 5) :
    ∑ z : Fin k → ZMod 5, χ (∑ j, z j * e j) = if e = 0 then (5 : ℂ) ^ k else 0 := by
  simp_rw [χ_sum]
  rw [← Fintype.prod_sum (fun j t ↦ χ (t * e j))]
  simp_rw [sum_χ_mul]
  split_ifs with he
  · simp [he]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
end AME125
