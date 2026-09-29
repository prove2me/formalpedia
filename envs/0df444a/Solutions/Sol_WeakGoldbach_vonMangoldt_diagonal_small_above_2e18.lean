-- Prove2me | solution 1 for WeakGoldbach.vonMangoldt_diagonal_small_above_2e18
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:33:51.912725+00:00
-- url     : https://prove2.me/submissions/b570cda9-239f-4089-a816-17c7ed76de1c

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    ((ArithmeticFunction.vonMangoldt m : Real) ^ 2) <=
      (1 / 4 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
        (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmLarge : (4096 : ℝ) ≤ m := by
    exact_mod_cast (show 4096 ≤ m by omega)
  let t : ℝ := (m : ℝ) ^ (1 / 4 : ℝ)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hm0 _
  have ht4 : t ^ 4 = (m : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    norm_num
  have ht2 : (64 : ℝ) ≤ t ^ 2 := by
    by_contra h
    have hlt : t ^ 2 < 64 := lt_of_not_ge h
    have hsq : (t ^ 2) ^ 2 < (64 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (sq_nonneg t) (by norm_num)).2 hlt
    nlinarith [ht4]
  have hlog : Real.log (m : ℝ) ≤ 4 * t := by
    have h := Real.log_le_rpow_div hm0 (show (0 : ℝ) < 1 / 4 by norm_num)
    dsimp [t]
    linarith
  have hLambda : ArithmeticFunction.vonMangoldt m ≤ 4 * t :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlog
  have hLambda0 : 0 ≤ ArithmeticFunction.vonMangoldt m :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hsquare : ArithmeticFunction.vonMangoldt m ^ 2 ≤ 16 * t ^ 2 := by
    nlinarith [sq_le_sq₀ hLambda0 (by positivity : 0 ≤ 4 * t) |>.2 hLambda]
  have hquarter : 16 * t ^ 2 ≤ (1 / 4 : ℝ) * (m : ℝ) := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2), ht4]
  have hprod : (1 : ℝ) ≤
      Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.one_le_prod
    intro p hp
    have hpNat : 2 < p := (Finset.mem_filter.mp hp).2
    have hpReal : (2 : ℝ) < p := by exact_mod_cast hpNat
    apply (one_le_div (by linarith : (0 : ℝ) < (p : ℝ) - 2)).2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hprod hm0
  nlinarith
