-- Prove2me | solution 1 for QuantumLTF.Membership.rho_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T18:57:52.200831+00:00
-- url     : https://prove2.me/submissions/4e936b29-2316-4fab-ab21-21a67030ea71

import Mathlib
import Definitions.Def_QuantumLTF_Membership_rho

open QuantumLTF.Membership

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    rho n * Real.sqrt n ≤ 1 / 40 := by
  let y : ℝ := 40 * Real.sqrt n
  let k : ℕ := ⌈Real.logb 2 y⌉₊
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hy : 0 < y := by dsimp [y]; positivity
  have hk : Real.logb 2 y ≤ (k : ℝ) := Nat.le_ceil _
  have hypowR : y ≤ (2 : ℝ) ^ (k : ℝ) :=
    (Real.logb_le_iff_le_rpow (b := 2) (x := y) (y := (k : ℝ)) (by norm_num) hy).1 hk
  have hypow : y ≤ (2 : ℝ) ^ k := by
    simpa [Real.rpow_natCast] using hypowR
  have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ y⁻¹ :=
    (inv_le_inv₀ (pow_pos (by norm_num) k) hy).2 hypow
  have hrho : rho n = ((2 : ℝ) ^ k)⁻¹ := by
    simp only [rho, k, y, inv_pow]
  rw [hrho]
  calc
    ((2 : ℝ) ^ k)⁻¹ * Real.sqrt n ≤ y⁻¹ * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hinv hsqrt.le
    _ = 1 / 40 := by
      dsimp [y]
      field_simp
