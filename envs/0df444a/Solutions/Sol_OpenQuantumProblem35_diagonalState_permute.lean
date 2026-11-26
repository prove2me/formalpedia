-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_permute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:27.393949+00:00
-- url     : https://prove2.me/submissions/75010532-c4de-4cb2-95b1-978a3454f2e7

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_isConstantConfig_permute_iff
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution (n d : ℕ) (π : Equiv.Perm (Fin n)) :
    permuteState π (diagonalState n d) = diagonalState n d := by
  ext x
  by_cases h : IsConstantConfig x
  · have h' : IsConstantConfig (permuteConfig π x) := (isConstantConfig_permute_iff π x).2 h
    simp [permuteState_apply, diagonalState_apply, h, h']
  · have h' : ¬ IsConstantConfig (permuteConfig π x) := by
      intro hx
      exact h ((isConstantConfig_permute_iff π x).1 hx)
    simp [permuteState_apply, diagonalState_apply, h, h']
end OpenQuantumProblem35
