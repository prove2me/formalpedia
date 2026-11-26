-- Prove2me | solution 1 for Sendov.log_sinh_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:42.602887+00:00
-- url     : https://prove2.me/submissions/d51c5152-be7f-4187-be45-9fd9240da705

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_Sendov_Common_Sinh
import Theorems.Thm_Sendov_sqrt_mul_sub_le

set_option autoImplicit false
open Sendov
open Real Set Filter
namespace Sendov
theorem _root_.solution {h : ℝ} (hh : 0 < h) :
    log (sinh h / h) ≤ sqrt (h ^ 2 + 9) - 3 := by
  set ψ : ℝ → ℝ := fun z => sqrt (z ^ 2 + 9) - 3 - (log (sinh z) - log z) with hψdef
  -- `ψ` has nonnegative derivative on `(0,∞)`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt ψ (z / sqrt (z ^ 2 + 9) - (cosh z / sinh z - 1 / z)) z := by
    intro z hz
    have hsinh : sinh z ≠ 0 := ne_of_gt (sinh_pos_iff.2 hz)
    apply HasDerivAt.sub
    · have h := (((hasDerivAt_pow 2 z).add_const 9).sqrt (ne_of_gt (by positivity))).sub_const 3
      refine h.congr_deriv ?_
      field_simp
      ring
    · exact (((hasDerivAt_sinh z).log hsinh).sub
        ((hasDerivAt_id' z).log (ne_of_gt hz))).congr_deriv (by field_simp)
  have hmono : MonotoneOn ψ (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (by rwa [interior_Ioi] at hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [interior_Ioi, mem_Ioi] at hz
    rw [(hderiv z hz).deriv, sub_nonneg, div_sub_div _ _ (ne_of_gt (sinh_pos_iff.2 hz))
      (ne_of_gt hz), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sqrt_mul_sub_le (le_of_lt hz)]
  -- `ψ → 0` as `z → 0⁺`
  have hslope : Tendsto (fun z => sinh z / z) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    simpa [slope_fun_def, div_eq_inv_mul, hasDerivAt_iff_tendsto_slope] using hasDerivAt_sinh 0
  have hlog : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
    have h1 : Tendsto (fun z => log (sinh z / z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp
        (hslope.mono_left hsub)
    have h2 : Tendsto (fun z : ℝ => sqrt (z ^ 2 + 9) - 3)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h9 : sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      have hc : ContinuousAt (fun z => sqrt (z ^ 2 + 9) - 3) 0 := by fun_prop
      simpa [ContinuousWithinAt, h9] using hc.continuousWithinAt (s := Ioi (0 : ℝ))
    have heq : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0),
        ψ z = (sqrt (z ^ 2 + 9) - 3) - log (sinh z / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hψdef, log_div (ne_of_gt (sinh_pos_iff.2 hz)) (ne_of_gt hz)]
    simpa [tendsto_congr' heq] using h2.sub h1
  -- combine
  have hev : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), ψ z ≤ ψ h := by
    have hmem : Ioo (0 : ℝ) h ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      mem_nhdsGT_iff_exists_Ioo_subset.2 (Exists.intro h (And.intro (mem_Ioi.2 hh) subset_rfl))
    filter_upwards [hmem] with z hz
    exact hmono (mem_Ioi.2 hz.1) (mem_Ioi.2 hh) (le_of_lt hz.2)
  have h0 : (0 : ℝ) ≤ ψ h := le_of_tendsto hlog hev
  have : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hh) hh
  rw [hψdef] at h0
  rw [log_div (ne_of_gt (sinh_pos_iff.2 hh)) (ne_of_gt hh)]
  linarith
end Sendov
