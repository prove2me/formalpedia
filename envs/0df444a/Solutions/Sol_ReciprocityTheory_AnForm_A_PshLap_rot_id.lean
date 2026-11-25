-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.rot_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:29.49626+00:00
-- url     : https://prove2.me/submissions/90536d8e-6bde-4475-95de-3cc627d66023

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (circleMap 0 1 θ) (circleMap 0 1 θ) +
      B (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) = B 1 1 + B Complex.I Complex.I := by
  have h1 : circleMap 0 1 θ = (Real.cos θ) • (1:ℂ) + (Real.sin θ) • Complex.I := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have h2 : circleMap 0 1 θ * Complex.I = (-Real.sin θ) • (1:ℂ) + (Real.cos θ) • Complex.I := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [h2, h1]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  linear_combination (B 1 1 + B Complex.I Complex.I) * Real.sin_sq_add_cos_sq θ
end ReciprocityTheory.AnForm.A.PshLap
