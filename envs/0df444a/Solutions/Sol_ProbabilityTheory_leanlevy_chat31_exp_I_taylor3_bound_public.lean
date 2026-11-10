-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat31_exp_I_taylor3_bound_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:56:20.398196+00:00
-- url     : https://prove2.me/submissions/fc865654-89a4-4357-91aa-5c48b163c8f8

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {z : ℝ} (hz : |z| ≤ 1) :
    ‖Complex.exp ((↑z : ℂ) * I) - 1 - (↑z : ℂ) * I + (↑z : ℂ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |z| ^ 3 := by
  set w : ℂ := (↑z : ℂ) * I with hw_def
  have hw_norm : ‖w‖ ≤ 1 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hz
  have hbound := Complex.exp_bound hw_norm (n := 3) (by decide)
  have hsum : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
    simp [Nat.factorial]
  rw [hsum] at hbound
  have hw_sq : w ^ 2 = -((↑z : ℂ) ^ 2) := by
    rw [hw_def, mul_pow, Complex.I_sq]; ring
  have hLHS : ‖Complex.exp w - (1 + w + w ^ 2 / 2)‖ =
      ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖ := by
    congr 1; rw [hw_sq]; ring
  rw [hLHS] at hbound
  have hw_pow : ‖w‖ ^ 3 = |z| ^ 3 := by
    rw [hw_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Complex.exp w - 1 - w + (↑z : ℂ) ^ 2 / 2‖
      ≤ ‖w‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((3 : ℕ).factorial * 3 : ℝ)⁻¹) := hbound
    _ = |z| ^ 3 * (4 / 18) := by rw [hw_pow]; norm_num [Nat.factorial]
    _ = (2 / 9 : ℝ) * |z| ^ 3 := by ring
