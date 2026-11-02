-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:50:26.039774+00:00
-- url     : https://prove2.me/submissions/9eb4acd6-96cd-4873-a890-cf6fba011add

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

private lemma abs_cos_pi_sub_half_lt_of_abs_lt {y c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
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

theorem solution (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hm : ¬ ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (b₀ : Bool)
    (hrun : IsRun 0 φ n b b₀) :
    |output n b b₀ - φ| ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have hloop : IsLoopRun 0 φ n b := hrun.1
  have hmain : ∀ m : ℕ, m < n →
      ∃ r : ℕ, r ≤ 1 ∧
        |(r : ℝ) + thetaAfter n b (n - 1 - m) - Int.fract ((2 : ℝ) ^ (n - 1 - m) * φ)| ≤
          ((2 : ℝ) ^ (m + 2))⁻¹ := by
    intro m
    induction m with
    | zero =>
      intro hm0
      simp only [Nat.sub_zero]
      set j := n - 1
      have hj : j < n := by omega
      have hjn : j + 1 = n := by omega
      have hadm := hloop j hj
      have hstep : thetaAfter n b j = bitVal (b j) / 2 := by
        rw [thetaAfter_step hj, hjn, thetaAfter_self]
        ring
      have hsig : sigma φ j (thetaAfter n b (j + 1) / 2) =
          |Real.cos (Real.pi * Int.fract ((2 : ℝ) ^ j * φ))| := by
        rw [hjn, thetaAfter_self, zero_div, sigma_eq_abs_cos_fract, sub_zero]
      set f := Int.fract ((2 : ℝ) ^ j * φ)
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have hpow : ((2 : ℝ) ^ (0 + 2))⁻¹ = 1 / 4 := by norm_num
      rw [hpow, hstep]
      cases hbj : b j
      · have hnotlt : ¬ (sigma φ j (thetaAfter n b (j + 1) / 2) < 1 / Real.sqrt 2) := by
          intro hlt
          have := hadm.1 (by linarith)
          rw [hbj] at this
          cases this
        rw [hsig, ← cos_pi_mul_quarter] at hnotlt
        have hnotmid : ¬ (|f - 1 / 2| < 1 / 4) := by
          intro hmid
          have hlt := abs_cos_pi_sub_half_lt_of_abs_lt (by norm_num) (by norm_num) hmid
          exact hnotlt (by convert hlt using 2; ring)
        have hsplit : f ≤ 1 / 4 ∨ 3 / 4 ≤ f := by
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
      · have hnotgt : ¬ (1 / Real.sqrt 2 < sigma φ j (thetaAfter n b (j + 1) / 2)) := by
          intro hgt
          have := hadm.2 (by linarith)
          rw [hbj] at this
          cases this
        rw [hsig, ← cos_pi_mul_quarter] at hnotgt
        have hfl : 1 / 4 ≤ f := by
          by_contra! hlow
          exact hnotgt (abs_cos_pi_gt_of_abs_lt (by norm_num) (abs_lt.mpr ⟨by linarith, by linarith⟩))
        have hfh : f ≤ 3 / 4 := by
          by_contra! hhigh
          exact hnotgt (abs_cos_pi_sub_one_gt_of_abs_lt (by norm_num)
            (abs_lt.mpr ⟨by linarith, by linarith⟩))
        simp only [bitVal, ↓reduceIte]
        refine ⟨0, by omega, ?_⟩
        push_cast
        rw [abs_le]
        constructor <;> linarith
    | succ m ih =>
      intro hm1
      obtain ⟨r', hr'1, ihr'⟩ := ih (by omega)
      set j := n - 1 - (m + 1)
      have hj : j < n := by omega
      have hj1 : j + 1 = n - 1 - m := by omega
      rw [← hj1] at ihr'
      obtain ⟨d, hd1, hfract⟩ := fract_two_pow_step φ j
      set f_j := Int.fract ((2 : ℝ) ^ j * φ)
      set f_j1 := Int.fract ((2 : ℝ) ^ (j + 1) * φ)
      set θ_j1 := thetaAfter n b (j + 1)
      set δ := (r' : ℝ) + θ_j1 - f_j1
      have hδ : |δ| ≤ ((2 : ℝ) ^ (m + 2))⁻¹ := ihr'
      have hpow_le : ((2 : ℝ) ^ (m + 2))⁻¹ ≤ 1 / 4 := by
        have : (4 : ℝ) ≤ (2 : ℝ) ^ (m + 2) := by
          have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (m + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          linarith [show (2 : ℝ) ^ 2 = 4 by norm_num]
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        linarith
      have hδ_quarter : |δ| / 2 < 1 / 4 := by linarith
      have hy_eq : f_j - θ_j1 / 2 = ((d : ℝ) + (r' : ℝ) - δ) / 2 := by
        dsimp [δ, f_j, f_j1]
        linarith [hfract]
      have hadm := hloop j hj
      have hsig : sigma φ j (θ_j1 / 2) = |Real.cos (Real.pi * (f_j - θ_j1 / 2))| :=
        sigma_eq_abs_cos_fract φ j (θ_j1 / 2)
      have hδ_half : |δ / 2| ≤ ((2 : ℝ) ^ (m + 1 + 2))⁻¹ := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have : ((2 : ℝ) ^ (m + 1 + 2))⁻¹ = ((2 : ℝ) ^ (m + 2))⁻¹ / 2 := by
          rw [pow_succ, mul_inv]
          ring
        linarith
      have hcases : (d = 0 ∧ r' = 0) ∨ (d + r' = 1) ∨ (d = 1 ∧ r' = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | hsum1 | ⟨rfl, rfl⟩
      · have hy_lt : |f_j - θ_j1 / 2| < 1 / 4 := by
          have : f_j - θ_j1 / 2 = -δ / 2 := by
            push_cast at hy_eq
            linarith [hy_eq]
          rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact hδ_quarter
        have hgt : 1 / Real.sqrt 2 < sigma φ j (θ_j1 / 2) := by
          rw [hsig, ← cos_pi_mul_quarter]
          exact abs_cos_pi_gt_of_abs_lt (by norm_num) hy_lt
        have hbj : b j = false := hadm.2 (by linarith)
        refine ⟨0, by omega, ?_⟩
        push_cast
        have hstep := thetaAfter_step hj b
        rw [hbj] at hstep
        simp only [bitVal, Bool.false_eq_true, ↓reduceIte, zero_div, add_zero] at hstep
        have heq : 0 + thetaAfter n b j - f_j = δ / 2 := by
          push_cast at hy_eq
          linarith [hstep, hy_eq]
        rw [heq]
        exact hδ_half
      · have hd_add_r : (d : ℝ) + (r' : ℝ) = 1 := by exact_mod_cast hsum1
        have hy_lt : |(f_j - θ_j1 / 2) - 1 / 2| < 1 / 4 := by
          have : (f_j - θ_j1 / 2) - 1 / 2 = -δ / 2 := by linarith [hy_eq, hd_add_r]
          rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact hδ_quarter
        have hlt : sigma φ j (θ_j1 / 2) < 1 / Real.sqrt 2 := by
          rw [hsig, ← cos_pi_mul_quarter]
          have h := abs_cos_pi_sub_half_lt_of_abs_lt (by norm_num) (by norm_num) hy_lt
          convert h using 2
          ring
        have hbj : b j = true := hadm.1 (by linarith)
        refine ⟨0, by omega, ?_⟩
        push_cast
        have hstep := thetaAfter_step hj b
        rw [hbj] at hstep
        simp only [bitVal, ↓reduceIte] at hstep
        have heq : 0 + thetaAfter n b j - f_j = δ / 2 := by
          linarith [hstep, hy_eq, hd_add_r]
        rw [heq]
        exact hδ_half
      · have hy_lt : |(f_j - θ_j1 / 2) - 1| < 1 / 4 := by
          have : (f_j - θ_j1 / 2) - 1 = -δ / 2 := by
            push_cast at hy_eq
            linarith [hy_eq]
          rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact hδ_quarter
        have hgt : 1 / Real.sqrt 2 < sigma φ j (θ_j1 / 2) := by
          rw [hsig, ← cos_pi_mul_quarter]
          exact abs_cos_pi_sub_one_gt_of_abs_lt (by norm_num) hy_lt
        have hbj : b j = false := hadm.2 (by linarith)
        refine ⟨1, by omega, ?_⟩
        push_cast
        have hstep := thetaAfter_step hj b
        rw [hbj] at hstep
        simp only [bitVal, Bool.false_eq_true, ↓reduceIte, zero_div, add_zero] at hstep
        have heq : 1 + thetaAfter n b j - f_j = δ / 2 := by
          push_cast at hy_eq
          linarith [hstep, hy_eq]
        rw [heq]
        exact hδ_half
  obtain ⟨r, hr1, hr⟩ := hmain (n - 1) (by omega)
  have h1 : n - 1 - (n - 1) = 0 := by omega
  have h2 : n - 1 + 2 = n + 1 := by omega
  rw [h1, h2, pow_zero, one_mul, Int.fract_eq_self.mpr ⟨hφ0, hφ1⟩] at hr
  set θ₀ := thetaAfter n b 0
  set δ := (r : ℝ) + θ₀ - φ
  have hpow_le : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ 1 / 4 := by
    have : (4 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (n + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hδ_quarter : |δ| / 2 < 1 / 4 := by linarith
  have hextra : extraSigma φ n b = |Real.cos (Real.pi * (φ / 2 - θ₀ / 2))| := by
    unfold extraSigma sigma
    simp [θ₀]
  have hadm₀ := hrun.2
  have hrcases : r = 0 ∨ r = 1 := by omega
  rcases hrcases with rfl | rfl
  · have hy_lt : |φ / 2 - θ₀ / 2| < 1 / 4 := by
      have : φ / 2 - θ₀ / 2 = -δ / 2 := by
        dsimp [δ]
        push_cast
        ring
      rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact hδ_quarter
    have hgt : 1 / Real.sqrt 2 < extraSigma φ n b := by
      rw [hextra, ← cos_pi_mul_quarter]
      exact abs_cos_pi_gt_of_abs_lt (by norm_num) hy_lt
    have hb₀ : b₀ = false := hadm₀.2 (by linarith)
    unfold output
    rw [hb₀]
    simp only [bitVal, Bool.false_eq_true, ↓reduceIte]
    convert hr using 2
    push_cast
    ring
  · have hy_lt : |(φ / 2 - θ₀ / 2) - 1 / 2| < 1 / 4 := by
      have : (φ / 2 - θ₀ / 2) - 1 / 2 = -δ / 2 := by
        dsimp [δ]
        push_cast
        ring
      rw [this, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact hδ_quarter
    have hlt : extraSigma φ n b < 1 / Real.sqrt 2 := by
      rw [hextra, ← cos_pi_mul_quarter]
      have h := abs_cos_pi_sub_half_lt_of_abs_lt (by norm_num) (by norm_num) hy_lt
      convert h using 2
      ring
    have hb₀ : b₀ = true := hadm₀.1 (by linarith)
    unfold output
    rw [hb₀]
    simp only [bitVal, ↓reduceIte]
    convert hr using 2
    push_cast
    ring
