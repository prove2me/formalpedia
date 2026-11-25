-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_maximal_ord_eq_1711457ea247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:35.469786+00:00
-- url     : https://prove2.me/submissions/89efae56-5cf6-499b-9f1c-8640a3c89bbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20


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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A)
    (P' : MaximalSpectrum (integralClosure B (FractionRing B))) :
    ∃ P : MaximalSpectrum (integralClosure A (FractionRing A)), ∀ a : A,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap A (integralClosure A (FractionRing A)) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap _ (Localization.AtPrime P'.asIdeal) (algebraMap B (integralClosure B (FractionRing B)) (π a))) := by
  obtain ⟨e, he1, hek, hsurj⟩ := exists_fracMap_unit π hπ hker
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap π hπ hker (x := 1) he1 hek (by rw [map_one]; exact isIntegral_one)
  have hφ : Function.Surjective (normMap π hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral A (e * x) :=
      isIntegral_mul_of_fracMap π hπ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨e * x, hint⟩, Subtype.ext ?_⟩
    show fracMap π hker (e * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap π hker ⟨e, he⟩ = 1 := Subtype.ext he1
  have hε : ∀ z, normMap π hker z = 0 → ⟨e, he⟩ * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have := P'.isMaximal
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap π hker) hφ ⟨e, he⟩ hε1 hε P'.asIdeal
  refine ⟨⟨P'.asIdeal.comap (normMap π hker), Ideal.comap_isMaximal_of_surjective _ hφ⟩, fun a ↦ ?_⟩
  rw [← ord_ringEquiv E, hE, normMap_algebraMap]
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
