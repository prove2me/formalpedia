-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthLocalizedQuotient_proof_73a8876f9733
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:30.619357+00:00
-- url     : https://prove2.me/submissions/8603ad4f-7a3b-4c2e-b20d-cedb27fc8bd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isNilpotent_of_minimalPrimes_eq_singleton_06d31625bdb3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_LocalizedQuotLength_proof_c7d52c028f3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
universe u
namespace GroundTheory.Heights₂.Heights
namespace LengthLocalizedQuotient
theorem _root_.solution (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm
end LengthLocalizedQuotient
end GroundTheory.Heights₂.Heights
