-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_analyticAt_of_exp_eq_f1c35840ad06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:40.222724+00:00
-- url     : https://prove2.me/submissions/d4f85a56-33ab-4cab-9974-0c515ebbcb66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g h : E → ℂ}
    {z₀ : E} (hg : ContinuousAt g z₀) (hh : AnalyticAt ℂ h z₀)
    (he : ∀ᶠ z in 𝓝 z₀, Complex.exp (g z) = h z) : AnalyticAt ℂ g z₀ := by
  have e₀ : Complex.exp (g z₀) = h z₀ := he.self_of_nhds
  have h0 : h z₀ ≠ 0 := e₀ ▸ Complex.exp_ne_zero _
  set L : E → ℂ := fun z => g z₀ + Complex.log (h z / h z₀) with hLdef
  have hL : AnalyticAt ℂ L z₀ := by
    refine analyticAt_const.add ((hh.div analyticAt_const h0).clog ?_)
    simp [h0]
  refine hL.congr ?_
  have hLz : L z₀ = g z₀ := by simp [hLdef, h0]
  have hg' : ∀ᶠ z in 𝓝 z₀, ‖g z - g z₀‖ < Real.pi := by
    have := hg.eventually (Metric.ball_mem_nhds (g z₀) Real.pi_pos)
    filter_upwards [this] with z hz
    simpa [dist_eq_norm] using hz
  have hL' : ∀ᶠ z in 𝓝 z₀, ‖L z - g z₀‖ < Real.pi := by
    have := hL.continuousAt.eventually (Metric.ball_mem_nhds (L z₀) Real.pi_pos)
    filter_upwards [this] with z hz
    simpa [dist_eq_norm, hLz] using hz
  filter_upwards [hg', hL', he] with z hgz hLz' hez
  have hz0 : h z ≠ 0 := hez ▸ Complex.exp_ne_zero _
  have hexp : Complex.exp (L z) = Complex.exp (g z) := by
    simp only [hLdef, Complex.exp_add, e₀, hez]
    rw [Complex.exp_log (div_ne_zero hz0 h0)]
    field_simp
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hnorm : ‖(m : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 * Real.pi := by
    have : (m : ℂ) * (2 * Real.pi * Complex.I) = (L z - g z₀) - (g z - g z₀) := by rw [hm]; ring
    rw [this]
    calc ‖(L z - g z₀) - (g z - g z₀)‖ ≤ ‖L z - g z₀‖ + ‖g z - g z₀‖ := norm_sub_le _ _
      _ < 2 * Real.pi := by linarith
  have hm0 : m = 0 := by
    have hpi := Real.pi_pos
    simp only [norm_mul, Complex.norm_intCast, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi] at hnorm
    have h1 : |(m : ℝ)| < 1 := by nlinarith
    rw [← Int.cast_abs] at h1
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  rw [hm, hm0]
  simp
end GroundTheory.Heights₂.Heights.Regular
