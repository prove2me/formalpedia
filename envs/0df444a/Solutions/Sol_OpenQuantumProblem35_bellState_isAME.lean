-- Prove2me | solution 1 for OpenQuantumProblem35.bellState_isAME
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:32.336204+00:00
-- url     : https://prove2.me/submissions/59ac2cbb-1997-4cdd-816f-64b1a6b3758c

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_isAME_of_div_two_eq_one
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
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) :
    IsAME (n := 2) (d := d) (bellState d) := by
  simpa [bellState] using
    diagonalState_isAME_of_div_two_eq_one (n := 2) (d := d) (by decide) (by norm_num) hd
end OpenQuantumProblem35
