-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:58.238399+00:00
-- url     : https://prove2.me/submissions/43131055-45be-425b-8a4f-76d5a3706ca1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedLocalized

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
universe u v
namespace GroundTheory.Heights₂.Heights
namespace LengthLocalizedLocalized
theorem _root_.solution (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by
  have h : Ideal.under B (P.map (algebraMap B (Localization.AtPrime Q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hP
      (Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP))
  have key : IsLocalization ((P.map (algebraMap B (Localization.AtPrime Q))).comap
        (algebraMap B (Localization.AtPrime Q))).primeCompl
      (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime Q.primeCompl _
  rw [Ideal.under] at h
  have e : P.primeCompl = ((P.map (algebraMap B (Localization.AtPrime Q))).comap
      (algebraMap B (Localization.AtPrime Q))).primeCompl :=
    Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h]
  rw [e]
  exact key
end LengthLocalizedLocalized
end GroundTheory.Heights₂.Heights
