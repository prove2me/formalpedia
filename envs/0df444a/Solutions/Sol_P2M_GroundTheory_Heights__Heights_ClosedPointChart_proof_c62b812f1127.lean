-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointChart_proof_c62b812f1127
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:41.469967+00:00
-- url     : https://prove2.me/submissions/40271bbb-21d5-4293-9901-81a59a39a4ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_ratio_mem_103cf4a641af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14


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
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ClosedPointChart
theorem _root_.solution (hU : ClosedPointUnitSection.Statement) : ClosedPointChart.Statement := by
  intro T _ K' _ _ y hy m hm
  obtain ⟨e, g, he, hg0, hgL, hW⟩ := hU T K' y hy m hm
  have := hm.isPrime
  obtain ⟨W, hBW, hBunit, hBlt⟩ := ClosedPointUnitSection.exists_valuationSubring (curveRing y) m
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W := by
    intro u
    apply W.mem_of_valuation_le_one
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr
      (ht u (Finset.mem_univ _))
  have hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
      exact hratio u
    | algebraMap r => rw [eq_intCast]; exact intCast_mem W r
    | add x z _ _ hx hz => exact add_mem hx hz
    | mul x z _ _ hx hz => exact mul_mem hx hz
  have hinv : y ⟨(), t⟩ ^ e / g ∈ W := hW W hBW hBunit t
  have hgt : g / y ⟨(), t⟩ ^ e ∈ W :=
    hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)
  have hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1 := by
    have h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1 := by
      rw [← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by
        field_simp [pow_ne_zero e hyt]]
      exact map_one _
    have h2 := (W.valuation_le_one_iff _).mpr hinv
    have h3 := (W.valuation_le_one_iff _).mpr hgt
    by_contra hne
    have h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)
    exact ne_of_lt h4 h1
  have hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 →
      y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t') := by
    intro u t' ht'
    have e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e =
        (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1) := by
      rw [div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]
    rw [e1]
    exact mul_mem (ClosedPointAffineChart.ratio_mem y t' u)
      (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)
  have hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e := mul_pow_sub_one (by omega) _
  obtain ⟨s0, hs0, hs0B⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)
  have ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m := by
    intro hmem
    have h1 := hBlt _ hmem
    change W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1
    rw [map_mul, hpow, hval, hBunit s0 hs0, one_mul] at h1
    exact lt_irrefl _ h1
  refine ⟨t, hyt, fun u => ?_⟩
  obtain ⟨su, hsu, hsuB⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)
  refine ⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩
  · rcases hm.isPrime.mem_or_mem hmem with h | h
    · exact hsu h
    · exact ha0 h
  · push_cast
    field_simp
end ClosedPointChart
end GroundTheory.Heights₂.Heights
