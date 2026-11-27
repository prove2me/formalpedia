-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.logLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:26.387294+00:00
-- url     : https://prove2.me/submissions/64aee5fc-568a-4428-a874-701e1457aa82

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLevi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llEv_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llLog_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llLog_deriv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llLog_deriv2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llShift_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_llSmoothR_ev
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_comp_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hEv : EvLeviStatement n M) (hCh : ChainStatement n M) : LogLeviStatement n M := by
  intro z g ph r ε hz hg hph hpsh hr hε x ξ
  set c : ℝ := ε ^ 2 with hc_def
  have hc : 0 < c := by positivity
  have hvs : SmoothR n z (ev n g ph r) := llSmoothR_ev n z g ph r hg hph
  have hk : ContDiff ℝ ∞ (llLog c) := llLog_contDiff hc
  have hlw : lw n g ph r ε = fun y => llLog c (ev n g ph r y) := by
    funext y
    have hy : -c / 2 ≤ ev n g ph r y := by linarith [llEv_nonneg n g ph r y]
    simp only [lw, llLog]
    rw [llShift_eq hc hy]
  set e := ev n g ph r x with he_def
  have he0 : 0 ≤ e := llEv_nonneg n g ph r x
  have ht : -c / 2 < e := by linarith
  have hQ : 0 < e + c := by linarith

  have hL : (Levi n z (lw n g ph r ε) x ξ).re =
      (e + c)⁻¹ * (Levi n z (ev n g ph r) x ξ).re -
        ((e + c) ^ 2)⁻¹ * ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 := by
    rw [hlw, hCh z hz (llLog c) (ev n g ph r) (by simpa using contDiff_infty.mp hk 2) hvs x ξ,
      llLog_deriv hc ht, llLog_deriv2 hc ht]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring

  have hD : dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ =
      (((e + c)⁻¹ : ℝ) : ℂ) * dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by
    rw [hlw]
    unfold dDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d_comp_real n z (llLog c) hk (ev n g ph r) (SmoothR.ckR n z 1 _ hvs) j x,
      llLog_deriv hc ht]
    ring
  have hN : ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 =
      ((e + c) ^ 2)⁻¹ * ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 := by
    rw [hD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ)]
    rw [mul_pow, inv_pow]
  obtain ⟨h1, h2⟩ := hEv z g ph r hz hg hph hr x ξ
  have hLp : 0 ≤ (Levi n z ph x ξ).re := hpsh x ξ
  rw [hN, hL]
  rw [← he_def] at h1 h2
  generalize (Levi n z (ev n g ph r) x ξ).re = A at h1 h2 ⊢
  generalize ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 = N at h1 h2 ⊢
  generalize (Levi n z ph x ξ).re = P at h1 h2 hLp ⊢
  have hQne : e + c ≠ 0 := hQ.ne'
  constructor
  · have key : N ≤ e * A + e * (e + c) * P := by
      nlinarith [mul_nonneg (mul_nonneg he0 hc.le) hLp]
    rw [← sub_nonneg]
    have hid : e * ((e + c)⁻¹ * A - ((e + c) ^ 2)⁻¹ * N + P) - c * (((e + c) ^ 2)⁻¹ * N) =
        (e * A + e * (e + c) * P - N) * (e + c)⁻¹ := by
      field_simp
      ring
    rw [hid]
    exact mul_nonneg (by linarith) (inv_nonneg.mpr hQ.le)
  · have key : 0 ≤ (e + c) * A + (e + c) ^ 2 * P - N := by
      nlinarith [mul_nonneg hc.le h2, mul_nonneg (mul_nonneg hQ.le hc.le) hLp]
    have hid : (e + c)⁻¹ * A - ((e + c) ^ 2)⁻¹ * N + P =
        ((e + c) * A + (e + c) ^ 2 * P - N) * ((e + c) ^ 2)⁻¹ := by
      field_simp
      ring
    rw [hid]
    exact mul_nonneg key (inv_nonneg.mpr (sq_nonneg _))
end ReciprocityTheory.L2DbarEstimates.I
