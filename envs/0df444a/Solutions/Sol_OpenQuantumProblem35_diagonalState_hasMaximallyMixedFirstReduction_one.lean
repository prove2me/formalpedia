-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_hasMaximallyMixedFirstReduction_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:46.418131+00:00
-- url     : https://prove2.me/submissions/c504ae98-4f02-4257-8348-3bdc2cca3753

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_uniformCoeff_mul_star
public import Theorems.Thm_OpenQuantumProblem35_constantCompletion_injective
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_combineFirst_one
public import Theorems.Thm_OpenQuantumProblem35_hasMaximallyMixedFirstReduction_of_completion
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
theorem _root_.solution {n d : ℕ} (hn : 2 ≤ n) :
    HasMaximallyMixedFirstReduction (n := n) (d := d) 1 (by omega) (diagonalState n d) := by
  apply hasMaximallyMixedFirstReduction_of_completion
    (n := n) (d := d) (m := 1) (hm := by omega)
    (ψ := diagonalState n d)
    (completion := constantCompletion (n := n) (d := d))
    (coeff := uniformCoeff d)
  · intro x z
    exact diagonalState_combineFirst_one (hn := by omega) x z
  · exact constantCompletion_injective (n := n) (d := d) hn
  · simpa [card_config] using uniformCoeff_mul_star d
end OpenQuantumProblem35
