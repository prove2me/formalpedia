-- Prove2me | solution 1 for Real.two_mul_sub_one_div_add_one_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:30:58.180649+00:00
-- url     : https://prove2.me/submissions/3272f603-2bbc-48d6-81a2-452efb4f5685

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

theorem solution {t : ℝ} (ht : 1 ≤ t) :
    2 * (t - 1) / (t + 1) ≤ Real.log t := by
  have hd : ∀ x : ℝ, 1 ≤ x →
      HasDerivAt (fun y : ℝ => Real.log y - 2 + 4 * (y + 1)⁻¹)
        ((x - 1) ^ 2 / (x * (x + 1) ^ 2)) x := by
    intro x hx
    have hx0' : (0:ℝ) < x := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hx0'
    have hx1 : x + 1 ≠ 0 := by positivity
    have h1 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h3 : HasDerivAt (fun y : ℝ => (y + 1)⁻¹) (-1 / (x + 1) ^ 2) x := h2.inv hx1
    have h4 := (h1.sub_const 2).add (h3.const_mul (4:ℝ))
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn (fun y : ℝ => Real.log y - 2 + 4 * (y + 1)⁻¹) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun x hx => ((hd x hx).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (1:ℝ) < x := hx
      exact ((hd x hx'.le).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : (1:ℝ) < x := hx
      rw [(hd x hx'.le).deriv]
      have hx0 : (0:ℝ) < x := by linarith
      exact div_nonneg (sq_nonneg _) (mul_nonneg hx0.le (sq_nonneg _))
  have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  simp only [Real.log_one] at h0
  norm_num at h0
  have ht1 : t + 1 ≠ 0 := by intro h; linarith
  have hrw : 2 * (t - 1) / (t + 1) = 2 - 4 * (t + 1)⁻¹ := by
    field_simp
    ring
  rw [hrw]
  linarith
