-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_free_5ba711a9e1d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:26.879926+00:00
-- url     : https://prove2.me/submissions/6d5af1bf-7f03-464e-bf15-6a63dafeceec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059

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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) {n : ℕ}
    {X : Type*} [AddCommGroup X] [Module C X] (e : X ≃ₗ[C] (Fin n → C ⧸ P)) :
    Module.length C (QuotSMulTop y X) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = n := by
  rw [(QuotSMulTop.congr y e).length_eq,
    (IsLocalizedModule.mapEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl X)
      (LocalizedModule.mkLinearMap P.primeCompl (Fin n → C ⧸ P)) (Localization.AtPrime P) e).length_eq]
  exact lengths_pi P hy hmax n
end GroundTheory.Heights₂.Heights.LengthCutGlobal
