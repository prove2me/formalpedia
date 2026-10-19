-- Prove2me | solution 1 for RareDisease.ExogOutcome.reduced_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:21:34.755884+00:00
-- url     : https://prove2.me/submissions/45ecd52b-edb6-4970-8433-3970057b6f5a

import Mathlib

namespace GLM5Rare

/-- for a policy share β and 0 < p < 1, the quantity `1 - (1 - β) p` is positive. -/
theorem qpos (β p : ℝ) (hβ : 0 ≤ β) (hp0 : 0 < p) (hp1 : p < 1) : 0 < 1 - (1 - β) * p := by
  have h1 : (1 - β) * p ≤ 1 * p := mul_le_mul_of_nonneg_right (show 1 - β ≤ 1 by linarith) hp0.le
  linarith [h1]

/-- `1 - (1 - β) p` is strictly increasing in β. -/
theorem qmono (β₁ β₂ p : ℝ) (h : β₁ < β₂) (hp0 : 0 < p) :
    (1 : ℝ) - (1 - β₁) * p < 1 - (1 - β₂) * p := by
  have hd : 0 < (β₂ - β₁) * p := mul_pos (by linarith) hp0
  linarith [hd]

/-- the cross-inequality used for `x ↦ x / (1 - x)²` on `[0,1)`. -/
theorem ulem (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) (hy1 : y < 1) :
    x * (1 - y) ^ 2 < y * (1 - x) ^ 2 := by
  have hm : (1 - y) ^ 2 < (1 - x) ^ 2 :=
    pow_lt_pow_left₀ (show 1 - y < 1 - x by linarith)
      (show 0 ≤ 1 - y by linarith) (by norm_num)
  have hyy : 0 < y := lt_of_le_of_lt hx hxy
  exact (mul_le_mul_of_nonneg_right (le_of_lt hxy) (sq_nonneg _)).trans_lt
    (mul_lt_mul_of_pos_left hm hyy)

end GLM5Rare

set_option linter.unusedVariables false

/-- §4.4, p. 15, after (20): the patient welfare
`W(α, β) = p (1 - (1 - β) p)³ / (4 (1 - α) k)` and the government's expenditure
`M(α, β) = α p² (1 - (1 - β) p)² / (4 (1 - α)² k) + β p² (1 - (1 - β) p)² / (2 (1 - α) k)`
of (20) are strictly increasing in `α ∈ [0,1)` for every fixed `β ∈ [0,1)`, and strictly
increasing in `β ∈ [0,1)` for every fixed `α ∈ [0,1)`. -/
theorem solution (k p : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun α : ℝ => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ α ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun β : ℝ => p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun α : ℝ => α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
          + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) ∧
    (∀ α ∈ Set.Ico (0 : ℝ) 1,
      StrictMonoOn (fun β : ℝ => α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
          + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k))
        (Set.Ico (0 : ℝ) 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- welfare is strictly increasing in α
  · rintro β ⟨hβ0, hβ1⟩
    intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have h1y : 0 < 1 - y := by linarith
    have hcy : 0 < 4 * (1 - y) * k := by nlinarith [mul_pos h1y hk]
    have hb : (1 - x) * k > (1 - y) * k :=
      mul_lt_mul_of_pos_right (show 1 - y < 1 - x by linarith) hk
    have hbc : 4 * (1 - y) * k < 4 * (1 - x) * k := by linarith [hb]
    have hq := GLM5Rare.qpos β p hβ0 hp0 hp1
    have hA : 0 < p * (1 - (1 - β) * p) ^ 3 := mul_pos hp0 (pow_pos hq 3)
    exact div_lt_div_of_pos_left hA hcy hbc
  -- welfare is strictly increasing in β
  · rintro α ⟨hα0, hα1⟩
    intro βx hx βy hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have hd : 0 < 4 * (1 - α) * k :=
      by nlinarith [mul_pos (show 0 < 1 - α by linarith [hα1]) hk]
    have hqx : 0 < 1 - (1 - βx) * p := GLM5Rare.qpos βx p hx0 hp0 hp1
    have hqy : 0 < 1 - (1 - βy) * p := GLM5Rare.qpos βy p hy0 hp0 hp1
    have hq12 : (1 : ℝ) - (1 - βx) * p < 1 - (1 - βy) * p := GLM5Rare.qmono βx βy p hxy hp0
    exact (div_lt_div_iff₀ hd hd).mpr
      (mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hq12 hqx.le (by norm_num)) hp0) hd)
  -- spending is strictly increasing in α
  · rintro β ⟨hβ0, hβ1⟩
    intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    set q := 1 - (1 - β) * p with hqdef
    have hq : 0 < q := GLM5Rare.qpos β p hβ0 hp0 hp1
    have h1x : 0 < 1 - x := by linarith
    have h1y : 0 < 1 - y := by linarith
    have hb1 : 0 < 4 * (1 - x) ^ 2 * k := by nlinarith [pow_pos h1x 2, hk]
    have hb2 : 0 < 4 * (1 - y) ^ 2 * k := by nlinarith [pow_pos h1y 2, hk]
    have huxy := GLM5Rare.ulem x y hx0 hxy hy1
    have hC : 0 < p ^ 2 * q ^ 2 * (4 * k) :=
      mul_pos (mul_pos (pow_pos hp0 2) (pow_pos hq 2)) (mul_pos (by norm_num) hk)
    have hprod : (x * p ^ 2 * q ^ 2) * (4 * (1 - y) ^ 2 * k)
        < (y * p ^ 2 * q ^ 2) * (4 * (1 - x) ^ 2 * k) := by
      rw [show (x * p ^ 2 * q ^ 2) * (4 * (1 - y) ^ 2 * k)
            = p ^ 2 * q ^ 2 * (4 * k) * (x * (1 - y) ^ 2) by ring,
          show (y * p ^ 2 * q ^ 2) * (4 * (1 - x) ^ 2 * k)
            = p ^ 2 * q ^ 2 * (4 * k) * (y * (1 - x) ^ 2) by ring]
      exact mul_lt_mul_of_pos_left huxy hC
    have t1 : x * p ^ 2 * q ^ 2 / (4 * (1 - x) ^ 2 * k)
        < y * p ^ 2 * q ^ 2 / (4 * (1 - y) ^ 2 * k) :=
      (div_lt_div_iff₀ hb1 hb2).mpr hprod
    have hd2y : 0 < 2 * (1 - y) * k := by nlinarith [mul_pos h1y hk]
    have h2 : (2 * (1 - y) * k) ≤ (2 * (1 - x) * k) :=
      mul_le_mul_of_nonneg_right (show 2 * (1 - y) ≤ 2 * (1 - x) by linarith) hk.le
    have hnum : 0 ≤ β * p ^ 2 * q ^ 2 := by
      have h2n := mul_nonneg hβ0 (mul_nonneg (sq_nonneg p) (sq_nonneg q))
      linarith [h2n]
    have t2 : β * p ^ 2 * q ^ 2 / (2 * (1 - x) * k)
        ≤ β * p ^ 2 * q ^ 2 / (2 * (1 - y) * k) :=
      div_le_div_of_nonneg_left hnum hd2y h2
    exact add_lt_add_of_lt_of_le t1 t2
  -- spending is strictly increasing in β
  · rintro α ⟨hα0, hα1⟩
    intro βx hx βy hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    set qx := 1 - (1 - βx) * p with hqxdef
    set qy := 1 - (1 - βy) * p with hqydef
    have hqx0 : 0 ≤ qx := by
      have hle := mul_le_mul_of_nonneg_right (show 1 - βx ≤ 1 by linarith) hp0.le
      have hqp : 0 < qx := by linarith [hle, hp1]
      linarith
    have hqy0 : 0 ≤ qy := by
      have hle := mul_le_mul_of_nonneg_right (show 1 - βy ≤ 1 by linarith) hp0.le
      have hqp : 0 < qy := by linarith [hle, hp1]
      linarith
    have hq12 : (1 : ℝ) - (1 - βx) * p < 1 - (1 - βy) * p := GLM5Rare.qmono βx βy p hxy hp0
    have hβy0 : 0 < βy := lt_of_le_of_lt hx0 hxy
    have hd1 : 0 < 4 * (1 - α) ^ 2 * k :=
      by nlinarith [pow_pos (show 0 < 1 - α by linarith [hα1]) 2, hk]
    have hposc : 0 ≤ α * p ^ 2 := mul_nonneg hα0 (pow_pos hp0 2).le
    have hle : (α * p ^ 2) * qx ^ 2 ≤ (α * p ^ 2) * qy ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hqx0 (le_of_lt hq12) 2) hposc
    have hprod : (α * p ^ 2 * qx ^ 2) * (4 * (1 - α) ^ 2 * k)
        ≤ (α * p ^ 2 * qy ^ 2) * (4 * (1 - α) ^ 2 * k) :=
      mul_le_mul_of_nonneg_right hle hd1.le
    have t1 : α * p ^ 2 * qx ^ 2 / (4 * (1 - α) ^ 2 * k)
        ≤ α * p ^ 2 * qy ^ 2 / (4 * (1 - α) ^ 2 * k) :=
      (div_le_div_iff₀ hd1 hd1).mpr hprod
    have hd2 : 0 < 2 * (1 - α) * k :=
      by nlinarith [mul_pos (show 0 < 1 - α by linarith [hα1]) hk]
    have hmq : βx * qx ^ 2 < βy * qy ^ 2 :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt hxy)
        (pow_lt_pow_left₀ hq12 hqx0 (by norm_num)) (sq_nonneg qx) hβy0
    have hprod2 : (βx * p ^ 2 * qx ^ 2) * (2 * (1 - α) * k)
        < (βy * p ^ 2 * qy ^ 2) * (2 * (1 - α) * k) := by
      rw [show (βx * p ^ 2 * qx ^ 2) * (2 * (1 - α) * k)
            = p ^ 2 * (2 * (1 - α) * k) * (βx * qx ^ 2) by ring,
          show (βy * p ^ 2 * qy ^ 2) * (2 * (1 - α) * k)
            = p ^ 2 * (2 * (1 - α) * k) * (βy * qy ^ 2) by ring]
      exact mul_lt_mul_of_pos_left hmq (mul_pos (pow_pos hp0 2) hd2)
    have t2 : βx * p ^ 2 * qx ^ 2 / (2 * (1 - α) * k)
        < βy * p ^ 2 * qy ^ 2 / (2 * (1 - α) * k) :=
      (div_lt_div_iff₀ hd2 hd2).mpr hprod2
    exact add_lt_add_of_le_of_lt t1 t2
