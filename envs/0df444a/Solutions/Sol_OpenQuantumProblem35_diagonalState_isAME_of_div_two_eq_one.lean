-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_isAME_of_div_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:52.487373+00:00
-- url     : https://prove2.me/submissions/9afcdc3e-0183-43ba-8e29-d2427cef6b4b

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_isNormalized
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_permute
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_hasMaximallyMixedFirstReduction_one
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
theorem _root_.solution {n d : ℕ}
    (hn : 2 ≤ n) (hhalf : n / 2 = 1) (hd : 2 ≤ d) :
    IsAME (n := n) (d := d) (diagonalState n d) := by
  refine ⟨?_, ?_⟩
  · have hd1 : 1 ≤ d := by omega
    exact diagonalState_isNormalized (n := n) (d := d) (by omega) hd1
  · intro π
    rw [diagonalState_permute n d π]
    simpa [hhalf] using
      diagonalState_hasMaximallyMixedFirstReduction_one (n := n) (d := d) hn
end OpenQuantumProblem35
