-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalizationPrimeDVR_proof_b56f011eeaa4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:49.334407+00:00
-- url     : https://prove2.me/submissions/050f24ee-1009-45a1-aba4-cfb92975ebd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalizationPrimeDVR

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
open IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace LocalizationPrimeDVR
theorem _root_.solution : LocalizationPrimeDVR.Statement := by
  intro R _ _ _ _ q p _ hq hp
  set O := Localization.AtPrime p
  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O,
      congrArg (Ideal.map (algebraMap R O)) hp, Ideal.map_span, Set.image_singleton]
  have hprin : (maximalIdeal O).IsPrincipal := ⟨⟨algebraMap R O q, hmax⟩⟩
  have hPID : IsPrincipalIdealRing O :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain O).out 4 0).mp hprin
  have hq0 : algebraMap R O q ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap R O) :=
      IsLocalization.injective O (p.primeCompl_le_nonZeroDivisors)
    exact hq.ne_zero (hinj (by rw [h, map_zero]))
  have hne : maximalIdeal O ≠ ⊥ := by
    rw [hmax, Ne, Ideal.span_singleton_eq_bot]
    exact hq0
  exact { hPID with not_a_field' := hne }
end LocalizationPrimeDVR
end GroundTheory.Heights₂.Heights
