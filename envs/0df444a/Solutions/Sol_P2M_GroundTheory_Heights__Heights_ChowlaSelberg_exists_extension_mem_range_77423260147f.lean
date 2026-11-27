-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_exists_extension_mem_range_77423260147f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:34.992777+00:00
-- url     : https://prove2.me/submissions/64c1a156-8fe6-47e5-94df-734dd508736f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PWIdealField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F : Type} [Field F] [NumberField F] (τ : F →+* ℂ) {z₁ z₂ : ℂ}
    (h₁ : IsAlgebraic ℚ z₁) (h₂ : IsAlgebraic ℚ z₂) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (j : F →+* F') (τ' : F' →+* ℂ),
      τ'.comp j = τ ∧ z₁ ∈ Set.range τ' ∧ z₂ ∈ Set.range τ' := by
  let e := AlgEquiv.ofInjectiveField τ.toRatAlgHom
  let E₁ : IntermediateField ℚ ℂ := τ.toRatAlgHom.fieldRange
  let E₂ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {z₁, z₂}
  have : FiniteDimensional ℚ E₁ := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : FiniteDimensional ℚ E₂ :=
    IntermediateField.finiteDimensional_adjoin_pair h₁.isIntegral h₂.isIntegral
  have : FiniteDimensional ℚ ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  have : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite ℚ _
  refine ⟨↥(E₁ ⊔ E₂), inferInstance, inferInstance,
    ((IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toRingHom.comp e.toRingEquiv.toRingHom),
    (E₁ ⊔ E₂).val.toRingHom, ?_, ?_, ?_⟩
  · ext x
    rfl
  · exact ⟨⟨z₁, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩
  · exact ⟨⟨z₂, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩
end GroundTheory.Heights₂.Heights.ChowlaSelberg
