-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:32.834856+00:00
-- url     : https://prove2.me/submissions/0c93678d-2267-4a34-b772-b7742b79e4e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul

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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  have hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hW
  have : IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))
  have : IsNoetherian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isNoetherian_quotient _
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]
  exact Module.length_ne_top
end GroundTheory.Heights₂.Heights.NumbersDVR
