-- Prove2me | solution 1 for QEC.Locality.AssumedBGKLMeasuredProfilePowerUpperBound.edgeRestricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:35:24.770078+00:00
-- url     : https://prove2.me/submissions/149d5bd3-1cf6-4147-9a5f-c681e8e35502

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_edgeRestricted_le


set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
namespace AssumedBGKLMeasuredProfilePowerUpperBound
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (edges : Finset (ι × ι)) :
    AssumedBGKLMeasuredProfilePowerUpperBound
      (edgeRestrictedGraph G edges) beta exponent := by
  refine ⟨hProfile.1, hProfile.2.1, hProfile.2.2.1, ?_⟩
  intro scale hscale hcard
  exact (Nat.cast_le.2 (twoThirdsSeparationProfile_edgeRestricted_le G edges scale)).trans
    (hProfile.2.2.2 scale hscale hcard)
end AssumedBGKLMeasuredProfilePowerUpperBound
end QEC.Locality
