-- Prove2me | solution 1 for OpenQuantumProblem35.not_existsAME_zero_dim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:43.129242+00:00
-- url     : https://prove2.me/submissions/f8198c92-aad7-4af8-9b44-53935910c6ee

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) : ¬ ExistsAME n 0 := by
  rintro ⟨ψ, hψ⟩
  let i0 : Fin n := ⟨0, hn⟩
  have : IsEmpty (Config n 0) := ⟨fun f => Fin.elim0 (f i0)⟩
  have hzero : ψ = 0 := by
    exact Subsingleton.elim _ _
  have : (0 : ℝ) = 1 := by
    simpa [IsNormalized, hzero] using hψ.1
  norm_num at this
end OpenQuantumProblem35
