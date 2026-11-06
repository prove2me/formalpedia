-- Prove2me | solution 1 for P2M_hh_integral__834b45965f6b
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:51.793073+00:00
-- url     : https://prove2.me/submissions/b89fb791-5995-4b31-9ca8-232f02ea88e1

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

theorem solution : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  let a : ℝ := 1 / (2 * π)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have h_change := integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := (Set.univ : Set ℝ))
    MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (hh a)
  change (∫ t in Ioi 0, hh a t) = 2 * π ^ 2
  calc
    (∫ t in Ioi 0, hh a t) = ∫ x : ℝ, |Real.exp x| • hh a (Real.exp x) := by
      simpa only [Set.image_univ, Real.range_exp, Measure.restrict_univ] using h_change
    _ = ∫ x : ℝ, (1 + (a * x) ^ 2)⁻¹ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [hh, abs_of_pos (Real.exp_pos x)]
      rw [mul_comm ((1 + (a * x) ^ 2)⁻¹) (Real.exp x)⁻¹, ← mul_assoc,
        mul_inv_cancel₀ (Real.exp_ne_zero x), one_mul]
    _ = |a⁻¹| • ∫ y : ℝ, (1 + y ^ 2)⁻¹ :=
      Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) a
    _ = 2 * π ^ 2 := by
      rw [integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr ha)]
      simp [a, smul_eq_mul]
      ring
