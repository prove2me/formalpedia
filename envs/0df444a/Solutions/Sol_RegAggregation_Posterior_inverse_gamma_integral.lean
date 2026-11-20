-- Prove2me | solution 1 for RegAggregation.Posterior.inverse_gamma_integral
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:52:42.430798+00:00
-- url     : https://prove2.me/submissions/caa94696-4957-43b4-be63-542e5d0539d3

import Mathlib
import Definitions.Def_RegAggregation_Posterior_Model

theorem _root_.solution (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-(s + 1)) * Real.exp (-c / x)) =
      ENNReal.ofReal (Real.Gamma s * c ^ (-s)) := by
  set g : ℝ → ℝ := fun y => y ^ (s - 1) * Real.exp (-(c * y)) with hg
  have hgi : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s - 1) (p := 1) (b := c)
      (by linarith) one_pos hc
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [hg, Real.rpow_one, neg_mul]
  have hfeq : Set.EqOn (fun x : ℝ => x ^ (-(s + 1)) * Real.exp (-c / x))
      (fun x => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) (Set.Ioi 0) := by
    intro x hx
    have hx : 0 < x := hx
    simp only [hg, smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul hx.le, Real.rpow_neg_one]
    rw [show -c / x = -(c * x⁻¹) by ring]
    rw [← mul_assoc, ← Real.rpow_add hx]
    congr 2
    ring
  have hfi : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(s + 1)) * Real.exp (-c / x))
      (Set.Ioi 0) :=
    ((MeasureTheory.integrableOn_Ioi_comp_rpow_iff g (by norm_num)).mpr hgi).congr_fun hfeq.symm measurableSet_Ioi
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi]
  · congr 1
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfeq,
      MeasureTheory.integral_comp_rpow_Ioi g (by norm_num), hg, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hc,
      one_div, Real.inv_rpow hc.le, Real.rpow_neg hc.le]
    ring
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx : 0 < x := hx
    positivity
