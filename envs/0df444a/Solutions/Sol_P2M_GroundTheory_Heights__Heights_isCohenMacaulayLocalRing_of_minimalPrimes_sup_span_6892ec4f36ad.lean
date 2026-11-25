-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:19.247801+00:00
-- url     : https://prove2.me/submissions/2fc47fa5-20ef-4c6c-acd4-441dca950f3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightOneGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightOneGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538


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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp
end GroundTheory.Heights₂.Heights
