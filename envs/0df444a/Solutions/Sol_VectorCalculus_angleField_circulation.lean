-- Prove2me | solution 1 for VectorCalculus.angleField_circulation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:22:57.991705+00:00
-- url     : https://prove2.me/submissions/2b4da2e6-93ff-4990-a600-045515431f3e

import Mathlib
import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad
import Definitions.Def_VectorCalculus_conservative
import Definitions.Def_VectorCalculus_angleField

open VectorCalculus

theorem solution (R : ℝ) (hR : 0 < R) :
    lineIntegral angleField (fun t => ![R * Real.cos t, R * Real.sin t]) 0 (2 * Real.pi)
      = 2 * Real.pi := by
  unfold lineIntegral
  have h : ∀ t : ℝ, (∑ i, angleField ((fun t => ![R * Real.cos t, R * Real.sin t]) t) i *
      deriv (fun s => (fun t => ![R * Real.cos t, R * Real.sin t]) s i) t) = 1 := by
    intro t
    have hR0 : R ≠ 0 := hR.ne'
    have hd0 : deriv (fun s => R * Real.cos s) t = -(R * Real.sin t) := by
      have := ((Real.hasDerivAt_cos t).const_mul R).deriv
      rw [this]; ring
    have hd1 : deriv (fun s => R * Real.sin s) t = R * Real.cos t := by
      have := ((Real.hasDerivAt_sin t).const_mul R).deriv
      rw [this]
    simp only [Fin.sum_univ_two, angleField, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    rw [hd0, hd1]
    have hsc := Real.sin_sq_add_cos_sq t
    have hden : (R * Real.cos t) ^ 2 + (R * Real.sin t) ^ 2 = R ^ 2 := by
      nlinarith [hsc]
    rw [hden]
    field_simp
    nlinarith [hsc]
  simp_rw [h]
  simp
