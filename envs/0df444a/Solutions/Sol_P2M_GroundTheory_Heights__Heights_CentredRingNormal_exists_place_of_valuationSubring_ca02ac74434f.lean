-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CentredRingNormal_exists_place_of_valuationSubring_ca02ac74434f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:37.297678+00:00
-- url     : https://prove2.me/submissions/7f4a970c-3d91-440f-8cb4-321f36e3eeed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7

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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
namespace GroundTheory.Heights₂.Heights.CentredRingNormal
theorem _root_.solution (V : ValuationSubring L) (hV : V ≠ ⊤) :
    ∃ w : FinitePlace L, ∀ x : L, x ∈ V ↔ w x ≤ 1 := by
  have hint : ∀ a : 𝓞 L, algebraMap (𝓞 L) L a ∈ V := fun a ↦ by
    have h : IsIntegral V (algebraMap (𝓞 L) L a) :=
      isIntegral_of_comp (Int.castRingHom V) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]
    exact y.2
  let φ : 𝓞 L →+* V := (algebraMap (𝓞 L) L).codRestrict V hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal V).comap φ
  have hinv : ∀ s : 𝓞 L, s ∉ P → (algebraMap (𝓞 L) L s)⁻¹ ∈ V := fun s hs ↦ by
    have h1 : V.valuation (φ s : L) = 1 := by
      rcases V.valuation_lt_one_or_eq_one (φ s) with h | h
      · exact absurd ((V.valuation_lt_one_iff (φ s)).mpr h) hs
      · exact h
    rw [← V.valuation_le_one_iff, map_inv₀]
    change (V.valuation (φ s : L))⁻¹ ≤ 1
    rw [h1, inv_one]
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hV
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have hbP : b ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hint a) (hinv b hbP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hle : HeightOneSpectrum.valuationSubringAtPrime L v ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    exact mul_mem (hint a) (hinv s hs)
  refine ⟨FinitePlace.mk v, fun x ↦ ?_⟩
  rw [← mem_valuationSubring_iff_place,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) v,
    ValuationSubring.eq_of_le_of_ne_top _ hle hV]
end GroundTheory.Heights₂.Heights.CentredRingNormal
