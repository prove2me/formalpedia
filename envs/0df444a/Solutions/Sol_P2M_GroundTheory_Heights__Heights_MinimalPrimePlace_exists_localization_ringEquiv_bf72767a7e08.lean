-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:02.743409+00:00
-- url     : https://prove2.me/submissions/dd843e16-ecf8-4ebb-ae9c-3d4f9fd5c790

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace

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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (ε : R) (hε1 : φ ε = 1) (hε : ∀ z, φ z = 0 → ε * z = 0) (P' : Ideal S)
    [P'.IsPrime] :
    ∃ E : Localization.AtPrime (P'.comap φ) ≃+* Localization.AtPrime P',
      ∀ r, E (algebraMap R _ r) = algebraMap S _ (φ r) := by
  let _ : Algebra R (Localization.AtPrime P') := ((algebraMap S (Localization.AtPrime P')).comp φ).toAlgebra
  have halg : ∀ r, algebraMap R (Localization.AtPrime P') r = algebraMap S _ (φ r) := fun _ ↦ rfl
  have : IsLocalization (P'.comap φ).primeCompl (Localization.AtPrime P') := by
    rw [isLocalization_iff]
    refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
    · rw [halg]
      exact IsLocalization.map_units (Localization.AtPrime P') (⟨φ y, y.2⟩ : P'.primeCompl)
    · obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective P'.primeCompl z
      obtain ⟨a, rfl⟩ := hφ b
      obtain ⟨c, hc⟩ := hφ (v : S)
      have hcP : c ∈ (P'.comap φ).primeCompl := by
        show φ c ∉ P'
        rw [hc]
        exact v.2
      refine ⟨(a, ⟨c, hcP⟩), ?_⟩
      simp only [halg, hc]
      exact IsLocalization.mk'_spec _ _ _
    · rw [halg, halg] at h
      obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists P'.primeCompl _).1 h
      obtain ⟨c0, hc0⟩ := hφ (c' : S)
      have hcP : ε * c0 ∈ (P'.comap φ).primeCompl := by
        show φ (ε * c0) ∉ P'
        rw [map_mul, hε1, one_mul, hc0]
        exact c'.2
      refine ⟨⟨ε * c0, hcP⟩, ?_⟩
      have hz := hε (c0 * (x - y)) (by rw [map_mul, map_sub, hc0, mul_sub, hc', sub_self])
      show ε * c0 * x = ε * c0 * y
      linear_combination hz
  exact ⟨(IsLocalization.algEquiv (P'.comap φ).primeCompl (Localization.AtPrime (P'.comap φ))
    (Localization.AtPrime P')).toRingEquiv, fun r ↦ AlgEquiv.commutes _ r⟩
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
