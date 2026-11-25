-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_tprod_one_sub_pow_eq_intSeriesEval_f6fd74baf778
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:10.257409+00:00
-- url     : https://prove2.me/submissions/b0fb2306-87a7-407c-9dc8-282079542f7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_prod_one_sub_pow_le_6387f8597f85

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) = intSeriesEval (pentagonalSeries ℤ) x := by
  set M := Real.exp (1 - ‖x‖)⁻¹
  have hgeo := summable_geometric_of_lt_one (norm_nonneg x) hx
  have hterm (k n : ℕ) :
      ‖x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ ‖x‖ ^ n * M := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le (by nlinarith : n ≤ (k + 1) * n))
      (norm_prod_one_sub_pow_le hx k n) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have hsum (k : ℕ) : Summable
      (fun n ↦ x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))) :=
    (hgeo.mul_right M).of_norm_bounded (hterm k)
  have hlhs (k : ℕ) : Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
    apply multipliable_one_add_of_summable (f := fun n ↦ -x ^ (n + k + 1))
    simpa [add_assoc] using (summable_nat_add_iff (k + 1)).mpr hgeo
  have htail : Tendsto (fun k ↦ (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : ℕ), x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k ↦ ‖x‖ ^ k * ∑' n, ‖x‖ ^ n * M) (fun k ↦ ?_) ?_
    · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      refine mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le ?_) ?_ (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
      · rw [Nat.le_div_iff_mul_le two_pos]; nlinarith
      · exact (norm_tsum_le_tsum_norm ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k))).trans ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k) |>.tsum_le_tsum (hterm k) (hgeo.mul_right M))
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const
        (∑' n, ‖x‖ ^ n * M)

  have hP : HasSum (fun n ↦ ((coeff n (pentagonalSeries ℤ) : ℤ) : ℂ) * x ^ n)
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    refine (Summable.of_norm ?_).hasSum
    simp only [norm_intSeries_term]
    exact intSeriesConv_pentagonalSeries (norm_nonneg x) hx
  rw [← pentagonal_injective.hasSum_iff fun n hn ↦ by
    simp [coeff_pentagonalSeries_eq_zero ℤ hn]] at hP
  rw [← neg_injective.hasSum_iff (fun y hy ↦ by absurd hy; use -y; simp)] at hP
  have hN := hP.nat_add_neg_add_one
  have hN' : HasSum (fun k : ℕ ↦ (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)))
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    convert hN using 1
    ext k
    simp_rw [Function.comp_apply, neg_neg, coeff_pentagonalSeries_pentagonal, Int.negOnePow_add]
    simp
    ring
  rw [Pentagonal.tprod_one_sub_pow (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx) hsum hlhs
    hN'.summable htail, hN'.tsum_eq]
end GroundTheory.Heights₂.Heights.ChowlaSelberg
