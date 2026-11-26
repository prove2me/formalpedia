-- Prove2me | solution 1 for OpenQuantumProblem35.permuteState_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:10.743597+00:00
-- url     : https://prove2.me/submissions/afea611f-5d28-47a7-ba0c-8ba64c943c9f

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteConfig_refl
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (ψ : StateVector n d) :
    permuteState (Equiv.refl (Fin n)) ψ = ψ := by
  ext x
  simp [permuteState_apply, permuteConfig_refl]
end OpenQuantumProblem35
