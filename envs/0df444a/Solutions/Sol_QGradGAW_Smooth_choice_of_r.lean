-- Prove2me | solution 1 for QGradGAW.Smooth.choice_of_r
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:34:20.379792+00:00
-- url     : https://prove2.me/submissions/1e3be0b1-1dd7-4668-b54b-0a5491805beb

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open QGradGAW.Smooth

theorem solution (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) (c ε : ℝ) (hε : 0 < ε) (hεc : ε ≤ c) :
    let A : ℝ := 81 * 8 * 42 * Real.pi * c * m * Real.sqrt d / ε
    let r : ℝ := 1 / (9 * c * m * Real.sqrt d * A ^ (1 / (2 * (m : ℝ))))
    8 * r * c * m * Real.sqrt d = 8 / 9 * A ^ (-(1 / (2 * (m : ℝ)))) ∧
      ∑' k : ℕ, (8 * r * c * m * Real.sqrt d) ^ (2 * m + 1 + k) ≤ ε * r / (8 * 42 * Real.pi) := by
  intro A r
  have hc : 0 < c := lt_of_lt_of_le hε hεc
  have hs : 1 ≤ Real.sqrt d := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_gt_three
  have hA : 0 < A := by positivity
  set s := Real.sqrt d with hsdef
  have hms : 1 ≤ (m:ℝ) * s := one_le_mul_of_one_le_of_one_le hmr hs
  have hcε : 1 ≤ c / ε := (one_le_div hε).mpr hεc
  have hAeq : A = (81 * 8 * 42 * Real.pi * ((m:ℝ) * s)) * (c / ε) := by
    simp only [A]; ring
  have hA1 : 1 ≤ A := by
    rw [hAeq]
    apply one_le_mul_of_one_le_of_one_le _ hcε
    nlinarith
  set R := A ^ (1 / (2 * (m : ℝ))) with hR
  have hRpos : 0 < R := Real.rpow_pos_of_pos hA _
  have hR1 : 1 ≤ R := Real.one_le_rpow hA1 (by positivity)
  have hRm : R ^ (2 * m) = A := by
    rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    have : (1 / (2 * (m : ℝ))) * ((2 * m : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hr : r = 1 / (9 * c * m * s * R) := rfl
  have hq : 8 * r * c * m * s = 8 / (9 * R) := by
    rw [hr]
    field_simp
  have hneg : A ^ (-(1 / (2 * (m : ℝ)))) = R⁻¹ := Real.rpow_neg hA.le _
  refine ⟨?_, ?_⟩
  · rw [hq, hneg]
    field_simp
  · rw [hq]
    set q : ℝ := 8 / (9 * R) with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hq89 : q ≤ 8 / 9 := by
      rw [hqdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hqR : q ≤ R⁻¹ := by
      rw [hqdef, div_le_iff₀ (by positivity)]
      have : R⁻¹ * (9 * R) = 9 := by field_simp
      nlinarith [inv_pos.mpr hRpos]
    have hq2m : q ^ (2 * m) ≤ A⁻¹ := by
      calc q ^ (2 * m) ≤ (R⁻¹) ^ (2 * m) := pow_le_pow_left₀ hq0 hqR _
        _ = A⁻¹ := by rw [inv_pow, hRm]
    have hts : ∑' k : ℕ, q ^ (2 * m + 1 + k) = q ^ (2 * m + 1) * (1 - q)⁻¹ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 (by linarith)]
    rw [hts]
    have h1q : (1 : ℝ) / 9 ≤ 1 - q := by linarith
    have hinv : (1 - q)⁻¹ ≤ 9 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hqpow : q ^ (2 * m + 1) ≤ q / A := by
      rw [pow_succ]
      calc q ^ (2 * m) * q ≤ A⁻¹ * q := by gcongr
        _ = q / A := by ring
    have hqA : q / A = r * ε / (81 * 42 * Real.pi) := by
      have hqq : q = 8 * r * c * m * s := hq.symm
      rw [hqq, hAeq]
      have : (0:ℝ) < c := hc
      field_simp
    have hr0 : 0 < r := by positivity
    calc q ^ (2 * m + 1) * (1 - q)⁻¹ ≤ (q / A) * 9 := by
          apply mul_le_mul hqpow hinv (by positivity) (by positivity)
      _ = r * ε / (9 * 42 * Real.pi) := by rw [hqA]; field_simp; ring
      _ ≤ ε * r / (8 * 42 * Real.pi) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 < r * ε * Real.pi := by positivity
          nlinarith
