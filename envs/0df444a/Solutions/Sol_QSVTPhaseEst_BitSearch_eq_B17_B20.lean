-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.eq_B17_B20
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:50:26.894012+00:00
-- url     : https://prove2.me/submissions/c713baec-54bc-4b0a-a746-e4585d5ca53b

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

open QSVTPhaseEst.BitSearch

private lemma thetaAfter_self (n : ℕ) (b : ℕ → Bool) : thetaAfter n b n = 0 := by
  simp [thetaAfter, thetaIter]

private lemma thetaAfter_step {n j : ℕ} (hj : j < n) (b : ℕ → Bool) :
    thetaAfter n b j = thetaAfter n b (j + 1) / 2 + bitVal (b j) / 2 := by
  unfold thetaAfter
  have h1 : n - j = (n - (j + 1)) + 1 := by omega
  have h2 : n - 1 - (n - (j + 1)) = j := by omega
  rw [h1, thetaIter, h2]

private lemma abs_cos_pi_add_int (y : ℝ) (k : ℤ) :
    |Real.cos (Real.pi * (y + k))| = |Real.cos (Real.pi * y)| := by
  have h : Real.pi * (y + k) = Real.pi * y + k * Real.pi := by ring
  rw [h, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

private lemma sigma_eq_abs_cos_fract (φ : ℝ) (j : ℕ) (θ : ℝ) :
    sigma φ j θ = |Real.cos (Real.pi * (Int.fract ((2 : ℝ) ^ j * φ) - θ))| := by
  unfold sigma
  have h : (2 : ℝ) ^ j * φ - θ =
      (Int.fract ((2 : ℝ) ^ j * φ) - θ) + (⌊(2 : ℝ) ^ j * φ⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [h, abs_cos_pi_add_int]

private lemma fract_two_mul_step (x : ℝ) :
    ∃ d : ℕ, d ≤ 1 ∧ Int.fract x = ((d : ℝ) + Int.fract (2 * x)) / 2 := by
  set k : ℤ := ⌊2 * x⌋ - 2 * ⌊x⌋
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (⌊2 * x⌋ : ℝ) ≤ 2 * x := Int.floor_le (2 * x)
  have h4 : 2 * x < (⌊2 * x⌋ : ℝ) + 1 := Int.lt_floor_add_one (2 * x)
  have hk_gt : (-1 : ℝ) < (k : ℝ) := by
    dsimp [k]
    push_cast
    linarith
  have hk_lt : (k : ℝ) < (2 : ℝ) := by
    dsimp [k]
    push_cast
    linarith
  have hk_gt' : -1 < k := by exact_mod_cast hk_gt
  have hk_lt' : k < 2 := by exact_mod_cast hk_lt
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with hk0 | hk1
  · refine ⟨0, by omega, ?_⟩
    have hk0' : (⌊2 * x⌋ : ℝ) - 2 * (⌊x⌋ : ℝ) = 0 := by
      exact_mod_cast show ⌊2 * x⌋ - 2 * ⌊x⌋ = (0 : ℤ) from hk0
    rw [Int.fract, Int.fract]
    push_cast
    linarith
  · refine ⟨1, by omega, ?_⟩
    have hk1' : (⌊2 * x⌋ : ℝ) - 2 * (⌊x⌋ : ℝ) = 1 := by
      exact_mod_cast show ⌊2 * x⌋ - 2 * ⌊x⌋ = (1 : ℤ) from hk1
    rw [Int.fract, Int.fract]
    push_cast
    linarith

private lemma fract_two_pow_step (φ : ℝ) (j : ℕ) :
    ∃ d : ℕ, d ≤ 1 ∧
      Int.fract ((2 : ℝ) ^ j * φ) = ((d : ℝ) + Int.fract ((2 : ℝ) ^ (j + 1) * φ)) / 2 := by
  have h : (2 : ℝ) ^ (j + 1) * φ = 2 * ((2 : ℝ) ^ j * φ) := by ring
  rw [h]
  exact fract_two_mul_step ((2 : ℝ) ^ j * φ)

private lemma abs_cos_pi_gt_of_abs_lt {y c : ℝ} (hc : c ≤ 1 / 2) (hy : |y| < c) :
    Real.cos (Real.pi * c) < |Real.cos (Real.pi * y)| := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : Real.cos (Real.pi * y) = Real.cos (Real.pi * |y|) := by
    rw [← Real.cos_abs (Real.pi * y), abs_mul, abs_of_pos hpi]
  have hlt : Real.cos (Real.pi * c) < Real.cos (Real.pi * |y|) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith
    · nlinarith
  exact hlt.trans_le (h1 ▸ le_abs_self _)

private lemma abs_cos_pi_sub_one_gt_of_abs_lt {y c : ℝ} (hc : c ≤ 1 / 2) (hy : |y - 1| < c) :
    Real.cos (Real.pi * c) < |Real.cos (Real.pi * y)| := by
  have h : Real.pi * y = Real.pi * (y - 1) + Real.pi := by ring
  rw [h, Real.cos_add_pi, abs_neg]
  exact abs_cos_pi_gt_of_abs_lt hc hy

private lemma abs_sin_eq_abs_sin_abs (t : ℝ) : |Real.sin t| = |Real.sin (|t|)| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, Real.sin_neg, abs_neg]

private lemma abs_cos_pi_sub_half_lt_of_abs_lt {y c : ℝ} (_hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hy : |y - 1 / 2| < c) :
    |Real.cos (Real.pi * y)| < Real.cos (Real.pi * (1 / 2 - c)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : Real.pi * y = Real.pi * (y - 1 / 2) + Real.pi / 2 := by ring
  rw [h1, Real.cos_add_pi_div_two, abs_neg, abs_sin_eq_abs_sin_abs, abs_mul, abs_of_pos hpi]
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * |y - 1 / 2|) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith
  rw [abs_of_nonneg hsin_nonneg, ← Real.cos_pi_div_two_sub]
  have h3 : Real.pi / 2 - Real.pi * |y - 1 / 2| = Real.pi * (1 / 2 - |y - 1 / 2|) := by ring
  rw [h3]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · nlinarith
  · have : 0 ≤ |y - 1 / 2| := abs_nonneg _
    nlinarith
  · nlinarith

private lemma cos_pi_mul_quarter : Real.cos (Real.pi * (1 / 4)) = 1 / Real.sqrt 2 := by
  have h : Real.pi * (1 / 4) = Real.pi / 4 := by ring
  rw [h, Real.cos_pi_div_four]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_eq_div_iff (by norm_num) (ne_of_gt hpos)]
  linarith

private lemma cos_five_add_cos_three :
    Real.cos (Real.pi * (1 / 2 - 3 / 16)) + Real.cos (3 * Real.pi / 16) <
      2 * (1 / Real.sqrt 2) := by
  have h1 : Real.cos (Real.pi * (1 / 2 - 3 / 16)) + Real.cos (3 * Real.pi / 16) =
      2 * Real.cos ((Real.pi * (1 / 2 - 3 / 16) + 3 * Real.pi / 16) / 2) *
        Real.cos ((Real.pi * (1 / 2 - 3 / 16) - 3 * Real.pi / 16) / 2) :=
    Real.cos_add_cos _ _
  have h2 : (Real.pi * (1 / 2 - 3 / 16) + 3 * Real.pi / 16) / 2 = Real.pi * (1 / 4) := by ring
  have h3 : (Real.pi * (1 / 2 - 3 / 16) - 3 * Real.pi / 16) / 2 = Real.pi / 16 := by ring
  rw [h1, h2, h3, cos_pi_mul_quarter]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_lt : Real.cos (Real.pi / 16) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
  have hsqrt_pos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  nlinarith

theorem solution (Δ φ : ℝ) (_hΔ0 : 0 ≤ Δ)
    (hΔ : Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2))
    (_hφ0 : 0 ≤ φ) (_hφ1 : φ < 1) (n : ℕ) (hn : 2 ≤ n)
    (b : ℕ → Bool) (hrun : IsLoopRun Δ φ n b) :
    ¬ InDeltaRegion Δ (sigma φ (n - 2) (thetaAfter n b (n - 1) / 2)) := by
  have hΔ_upper : 1 / Real.sqrt 2 + Δ / 2 < Real.cos (Real.pi * (3 / 16)) := by
    have : Real.pi * (3 / 16) = 3 * Real.pi / 16 := by ring
    rw [this]
    linarith
  have hΔ_lower : Real.cos (Real.pi * (1 / 2 - 3 / 16)) < 1 / Real.sqrt 2 - Δ / 2 := by
    linarith [cos_five_add_cos_three]
  -- Step 1: j = n - 1
  have hj1 : n - 1 < n := by omega
  have hjn : (n - 1) + 1 = n := by omega
  have hadm1 := hrun (n - 1) hj1
  have hstep1 : thetaAfter n b (n - 1) = bitVal (b (n - 1)) / 2 := by
    rw [thetaAfter_step hj1, hjn, thetaAfter_self]
    ring
  have hsig1 : sigma φ (n - 1) (thetaAfter n b ((n - 1) + 1) / 2) =
      |Real.cos (Real.pi * Int.fract ((2 : ℝ) ^ (n - 1) * φ))| := by
    rw [hjn, thetaAfter_self, zero_div, sigma_eq_abs_cos_fract, sub_zero]
  set f1 := Int.fract ((2 : ℝ) ^ (n - 1) * φ)
  have hf1_0 : 0 ≤ f1 := Int.fract_nonneg _
  have hf1_1 : f1 < 1 := Int.fract_lt_one _
  have hr1_exists : ∃ r' : ℕ, r' ≤ 1 ∧
      |(r' : ℝ) + thetaAfter n b (n - 1) - f1| ≤ 5 / 16 := by
    rw [hstep1]
    cases hbj : b (n - 1)
    · have hnotlt : ¬ (sigma φ (n - 1) (thetaAfter n b ((n - 1) + 1) / 2) <
          1 / Real.sqrt 2 - Δ / 2) := by
        intro hlt
        have := hadm1.1 hlt
        rw [hbj] at this
        cases this
      rw [hsig1] at hnotlt
      have hnotmid : ¬ (|f1 - 1 / 2| < 3 / 16) := by
        intro hmid
        have hlt := abs_cos_pi_sub_half_lt_of_abs_lt (by norm_num) (by norm_num) hmid
        exact hnotlt (hlt.trans hΔ_lower)
      have hsplit : f1 ≤ 5 / 16 ∨ 11 / 16 ≤ f1 := by
        by_contra! h
        exact hnotmid (abs_lt.mpr ⟨by linarith, by linarith⟩)
      simp only [bitVal, Bool.false_eq_true, ↓reduceIte, zero_div, add_zero]
      rcases hsplit with hfle | hfge
      · refine ⟨0, by omega, ?_⟩
        push_cast
        rw [abs_le]
        constructor <;> linarith
      · refine ⟨1, by omega, ?_⟩
        push_cast
        rw [abs_le]
        constructor <;> linarith
    · have hnotgt : ¬ (1 / Real.sqrt 2 + Δ / 2 <
          sigma φ (n - 1) (thetaAfter n b ((n - 1) + 1) / 2)) := by
        intro hgt
        have := hadm1.2 hgt
        rw [hbj] at this
        cases this
      rw [hsig1] at hnotgt
      have hfl : 3 / 16 ≤ f1 := by
        by_contra! hlow
        have habs : |f1| < 3 / 16 := abs_lt.mpr ⟨by linarith, by linarith⟩
        have hgt := abs_cos_pi_gt_of_abs_lt (by norm_num) habs
        exact hnotgt (hΔ_upper.trans hgt)
      have hfh : f1 ≤ 13 / 16 := by
        by_contra! hhigh
        have habs : |f1 - 1| < 3 / 16 := abs_lt.mpr ⟨by linarith, by linarith⟩
        have hgt := abs_cos_pi_sub_one_gt_of_abs_lt (by norm_num) habs
        exact hnotgt (hΔ_upper.trans hgt)
      simp only [bitVal, ↓reduceIte]
      refine ⟨0, by omega, ?_⟩
      push_cast
      rw [abs_le]
      constructor <;> linarith
  -- Step 2: j = n - 2
  obtain ⟨r', hr'1, hδ⟩ := hr1_exists
  have hj2_succ : (n - 2) + 1 = n - 1 := by omega
  obtain ⟨d, hd1, hfract⟩ := fract_two_pow_step φ (n - 2)
  rw [hj2_succ] at hfract
  set f2 := Int.fract ((2 : ℝ) ^ (n - 2) * φ)
  set θ1 := thetaAfter n b (n - 1)
  set δ := (r' : ℝ) + θ1 - f1
  have hδ_lt : |δ| / 2 < 3 / 16 := by linarith
  have hy_eq : f2 - θ1 / 2 = ((d : ℝ) + (r' : ℝ) - δ) / 2 := by
    dsimp [δ, f2, f1]
    linarith [hfract]
  have hsig2 : sigma φ (n - 2) (θ1 / 2) = |Real.cos (Real.pi * (f2 - θ1 / 2))| :=
    sigma_eq_abs_cos_fract φ (n - 2) (θ1 / 2)
  have hcases : (d = 0 ∧ r' = 0) ∨ (d + r' = 1) ∨ (d = 1 ∧ r' = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | hsum1 | ⟨rfl, rfl⟩
  · have hy_lt : |f2 - θ1 / 2| < 3 / 16 := by
      have : f2 - θ1 / 2 = -δ / 2 := by
        push_cast at hy_eq
        linarith [hy_eq]
      rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact hδ_lt
    have hgt : 1 / Real.sqrt 2 + Δ / 2 < sigma φ (n - 2) (θ1 / 2) := by
      rw [hsig2]
      exact hΔ_upper.trans (abs_cos_pi_gt_of_abs_lt (by norm_num) hy_lt)
    intro hreg
    linarith [hreg.2]
  · have hd_add_r : (d : ℝ) + (r' : ℝ) = 1 := by exact_mod_cast hsum1
    have hy_lt : |(f2 - θ1 / 2) - 1 / 2| < 3 / 16 := by
      have : (f2 - θ1 / 2) - 1 / 2 = -δ / 2 := by linarith [hy_eq, hd_add_r]
      rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact hδ_lt
    have hlt : sigma φ (n - 2) (θ1 / 2) < 1 / Real.sqrt 2 - Δ / 2 := by
      rw [hsig2]
      exact (abs_cos_pi_sub_half_lt_of_abs_lt (by norm_num) (by norm_num) hy_lt).trans hΔ_lower
    intro hreg
    linarith [hreg.1]
  · have hy_lt : |(f2 - θ1 / 2) - 1| < 3 / 16 := by
      have : (f2 - θ1 / 2) - 1 = -δ / 2 := by
        push_cast at hy_eq
        linarith [hy_eq]
      rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact hδ_lt
    have hgt : 1 / Real.sqrt 2 + Δ / 2 < sigma φ (n - 2) (θ1 / 2) := by
      rw [hsig2]
      exact hΔ_upper.trans (abs_cos_pi_sub_one_gt_of_abs_lt (by norm_num) hy_lt)
    intro hreg
    linarith [hreg.2]
