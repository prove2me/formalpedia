-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_sep_7bec6285acde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:25.185126+00:00
-- url     : https://prove2.me/submissions/944d9b5f-177d-4470-9ed2-8fa091c03110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_iff_3571b1996383
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_pow_sub_one_ab4b1a690500

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) {P P' : HeightOneSpectrum (𝓞 K')} {d : ℕ}
    {G : K'} (hG : G ∈ chartLat y 1 d) (h1 : IsUnitAt y P' d G) (h2 : ¬IsUnitAt y P d G) :
    ∃ (k : ℕ) (h : K'), h ∈ chartLat y 1 k ∧ IsUnitAt y P k h ∧ ¬IsUnitAt y P' k h := by
  by_contra H
  push Not at H
  obtain ⟨t, ht0, ht⟩ := exists_max y hy P
  have htP' : ∀ u, P'.valuation K' (y ⟨(), u⟩) ≤ P'.valuation K' (y ⟨(), t⟩) := by
    have := H 1 _ (coord_mem y t) (fun u => by simpa using ht u)
    intro u
    simpa using this u
  have hyt : P'.valuation K' (y ⟨(), t⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hyt' : P.valuation K' (y ⟨(), t⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hxR : G / y ⟨(), t⟩ ^ d ∈ chartRingZ y (fun _ => t) := (mem_chartLat_iff y).mp hG t ht0
  have hx' : P'.valuation K' (G / y ⟨(), t⟩ ^ d) = 1 := by
    rw [map_div₀, map_pow]
    exact (div_eq_one_iff_eq (pow_ne_zero _ hyt)).mpr (le_antisymm (le_of_mem y ht0 htP' hG) (h1 t))
  have hx : P.valuation K' (G / y ⟨(), t⟩ ^ d) < 1 := by
    rw [isUnitAt_iff y ht, not_le] at h2
    rw [map_div₀, map_pow]
    exact (div_lt_one₀ (zero_lt_iff.mpr (pow_ne_zero _ hyt'))).mpr h2
  obtain ⟨N, hN, hxN⟩ := exists_pow_sub_one P' hx'
  have hwR : (G / y ⟨(), t⟩ ^ d) ^ N - 1 ∈ chartRingZ y (fun _ => t) :=
    sub_mem (pow_mem hxR N) (one_mem _)
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_chartLat y t ht0 hwR
  have hw : P.valuation K' ((G / y ⟨(), t⟩ ^ d) ^ N - 1) = 1 := by
    rw [← Valuation.map_neg, neg_sub]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_pow]
    exact pow_lt_one₀ zero_le hx (by omega)
  have hu := H k _ hk ((isUnitAt_iff y ht).mpr (le_of_eq (by rw [map_mul, hw, one_mul, map_pow])))
  rw [isUnitAt_iff y htP', map_mul, map_pow] at hu
  have hpos : 0 < P'.valuation K' (y ⟨(), t⟩) ^ k := zero_lt_iff.mpr (pow_ne_zero _ hyt)
  have hlt := mul_lt_mul_of_pos_right hxN hpos
  rw [one_mul] at hlt
  exact absurd hu (not_le.mpr hlt)
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
