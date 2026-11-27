-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NoCommonComponentCase_proof_dd76019d14e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:27.179711+00:00
-- url     : https://prove2.me/submissions/313f1909-4208-43a5-90ae-0f11f4789ea2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMore
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealCorresp_proof_bd738eb41ba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealMultiHomog_proof_41306882bd1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6


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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace NoCommonComponentCase
theorem _root_.solution (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno L
  unfold cutIdentity
  rw [h₁ O ϖ hϖ K ι P d hP b f g hD.1 c s hs hsP hno L,
    h₂ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno L]
  unfold cycEval
  refine finsum_congr fun U => ?_
  beta_reduce
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧
      ¬ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)
  ·
    obtain ⟨hUp, hUm, -, hϖU, hdim⟩ := hU
    have hv : vNum U L = 0 := by
      refine h₄ _ K ι d (specialIdeal U) (SpecialIdealCorresp.proof O ϖ hϖ K ι ⊥ U hUp hϖU).1
        (SpecialIdealMultiHomog.proof O K ι U hUm) (Or.inr ?_) L
      rw [SpecialQuotDim.proof O ϖ hϖ K ι U hϖU]
      exact lt_of_not_ge hdim
    rw [hv, mul_zero, mul_zero]
  ·
    have e := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno U fun hp hm hr hϖU => by
      by_contra h
      exact hU ⟨hp, hm, hr, hϖU, h⟩
    unfold cycEval at e
    rw [e]
end NoCommonComponentCase
end GroundTheory.Heights₂.Heights.NumbersDVR
