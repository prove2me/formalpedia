-- Prove2me | solution 1 for TunnellMap.assemble_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:51.67626+00:00
-- url     : https://prove2.me/submissions/250c844e-fd54-4fb0-a4e0-f344fd1630ac

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_assemble_fiber_iff
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply


attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr

set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}
namespace TunnellMap
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A) (a : A) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      assemble even odd x₁ = a ∧
      assemble even odd x₂ = a ∧
      ∀ x, assemble even odd x = a ↔ x = x₁ ∨ x = x₂ := by
  refine ⟨Sum.inl (even.symm a), Sum.inr (odd.symm a), ?_, by simp,
    by simp, ?_⟩
  · simp
  · intro x
    exact assemble_fiber_iff even odd a x
end TunnellMap
