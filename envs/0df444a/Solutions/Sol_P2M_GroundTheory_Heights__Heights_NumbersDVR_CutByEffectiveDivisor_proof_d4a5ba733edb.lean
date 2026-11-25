-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByEffectiveDivisor_proof_d4a5ba733edb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:28:00.924136+00:00
-- url     : https://prove2.me/submissions/722b7bac-ef94-4516-9d25-69cebbec3d90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByEffectiveDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace CutByEffectiveDivisor
theorem _root_.solution (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2
end CutByEffectiveDivisor
end GroundTheory.Heights₂.Heights.NumbersDVR
