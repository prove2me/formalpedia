-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.operatorPowers_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:15:08.361489+00:00
-- url     : https://prove2.me/submissions/80282674-fce9-4f0e-b5c1-f4b5596dadf1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
open QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

theorem g67f2_pow_le {K : Type u} [RCLike K]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V]
    (x : V →L[K] V) (M : ℝ) (hM : 1 ≤ M) (hx : ‖x‖ ≤ M) (k : ℕ) : ‖x ^ k‖ ≤ M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ]
    calc ‖x ^ k * x‖ ≤ ‖x ^ k‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ M ^ k * M := by
          apply mul_le_mul ih hx (norm_nonneg _) (by positivity)
      _ = M ^ (k + 1) := by rw [pow_succ]

/-- Lemma 8.1, PDF p. 24: a small-time power bound and a one-step
exponential bound imply a global exponential power bound. No continuity
or differentiability of F is assumed. Powers are composition powers. -/
theorem solution
    {K : Type u} [RCLike K]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace K V] [CompleteSpace V]
    (F : Set.Ici (0 : ℝ) → (V →L[K] V)) (M a : ℝ) (hM : 0 < M)
    (hZero : F ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl)⟩ = 1)
    (hOne : ∀ t : Set.Ici (0 : ℝ), ‖F t‖ ≤ M * Real.exp (a * t.val))
    (hSmall : ∀ t : Set.Ici (0 : ℝ), ∀ n : ℕ, 0 < n →
      t.val * (n : ℝ) ≤ 1 → ‖F t ^ n‖ ≤ M) :
    ∃ omega : ℝ, ∀ t : Set.Ici (0 : ℝ), ∀ n : ℕ, 0 < n →
      ‖F t ^ n‖ ≤ M * Real.exp (omega * (n : ℝ) * t.val) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨0, fun t n _ => ?_⟩
    have : F t ^ n = 0 := by ext x; exact Subsingleton.elim _ _
    rw [this, norm_zero]; positivity
  have hM1 : 1 ≤ M := by
    have h := hOne ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl)⟩
    simp only [hZero, mul_zero, Real.exp_zero, mul_one] at h
    have h1 : ‖(1 : V →L[K] V)‖ = 1 := ContinuousLinearMap.norm_id
    linarith
  set c := Real.log M with hc
  have hc0 : 0 ≤ c := Real.log_nonneg hM1
  have hMp : ∀ k : ℕ, M ^ k = Real.exp (k * c) := fun k => by
    rw [hc, Real.exp_nat_mul, Real.exp_log hM]
  refine ⟨2 * c + |a|, fun t n hn => ?_⟩
  have ht0 : 0 ≤ t.val := t.property
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hω : 0 ≤ (2 * c + |a|) * (n : ℝ) * t.val := by positivity
  by_cases hA : t.val * (n : ℝ) ≤ 1
  · calc ‖F t ^ n‖ ≤ M := hSmall t n hn hA
      _ ≤ M * Real.exp ((2 * c + |a|) * (n : ℝ) * t.val) := by
          have := Real.one_le_exp hω
          nlinarith
  push_neg at hA
  have htpos : 0 < t.val := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hA; linarith
  by_cases hB : t.val ≤ 1
  · set m := ⌊1 / t.val⌋₊ with hm
    have h1t : 1 ≤ 1 / t.val := by rw [le_div_iff₀ htpos]; linarith
    have hm1 : 1 ≤ m := Nat.le_floor (by simpa using h1t)
    have hmle : (m : ℝ) ≤ 1 / t.val := Nat.floor_le (by positivity)
    have hlt : 1 / t.val < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmt : (m : ℝ) * t.val ≤ 1 := by
      calc (m : ℝ) * t.val ≤ 1 / t.val * t.val := by gcongr
        _ = 1 := by field_simp
    have hm1t : 1 < ((m : ℝ) + 1) * t.val := by
      calc (1 : ℝ) = 1 / t.val * t.val := by field_simp
        _ < ((m : ℝ) + 1) * t.val := by gcongr
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h2mt : 1 ≤ 2 * (m : ℝ) * t.val := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm1r) htpos.le]
    obtain ⟨q, r, hr, hnqr⟩ : ∃ q r, r < m ∧ n = m * q + r :=
      ⟨n / m, n % m, Nat.mod_lt _ (by omega), (Nat.div_add_mod n m).symm⟩
    have hdecomp : F t ^ n = (F t ^ m) ^ q * F t ^ r := by
      rw [hnqr, pow_add, pow_mul]
    have hFm : ‖F t ^ m‖ ≤ M := hSmall t m (by omega) (by rw [mul_comm]; exact hmt)
    have hFr : ‖F t ^ r‖ ≤ M := by
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · rw [hr0, pow_zero]; exact ContinuousLinearMap.norm_id_le.trans hM1
      · apply hSmall t r hr0
        have : (r : ℝ) ≤ m := by exact_mod_cast hr.le
        nlinarith
    have hnr : (n : ℝ) = m * q + r := by exact_mod_cast hnqr
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hq : (q : ℝ) * m ≤ n := by rw [hnr]; nlinarith
    have hqle : (q : ℝ) ≤ 2 * n * t.val := by
      nlinarith [mul_le_mul_of_nonneg_left h2mt hq0,
        mul_le_mul_of_nonneg_right hq (show (0:ℝ) ≤ 2 * t.val by positivity)]
    calc ‖F t ^ n‖ ≤ ‖(F t ^ m) ^ q‖ * ‖F t ^ r‖ := by rw [hdecomp]; exact norm_mul_le _ _
      _ ≤ M ^ q * M := by
          apply mul_le_mul (g67f2_pow_le _ M hM1 hFm q) hFr (norm_nonneg _) (by positivity)
      _ = M * Real.exp (q * c) := by rw [hMp]; ring
      _ ≤ M * Real.exp ((2 * c + |a|) * (n : ℝ) * t.val) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          apply Real.exp_le_exp.mpr
          have : 0 ≤ |a| * n * t.val := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hqle hc0]
  · push_neg at hB
    calc ‖F t ^ n‖ ≤ ‖F t‖ ^ n := norm_pow_le' _ hn
      _ ≤ (M * Real.exp (a * t.val)) ^ n := pow_le_pow_left₀ (norm_nonneg _) (hOne t) n
      _ = M * Real.exp (((n : ℝ) - 1) * c + a * t.val * n) := by
          rw [mul_pow, ← pow_sub_one_mul hn.ne' M, hMp, ← Real.exp_nat_mul, Real.exp_add,
            Nat.cast_sub (by omega : 1 ≤ n)]
          push_cast
          ring_nf
      _ ≤ M * Real.exp ((2 * c + |a|) * (n : ℝ) * t.val) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          apply Real.exp_le_exp.mpr
          have h1 : a * t.val * n ≤ |a| * t.val * n := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self a) ht0)
              (by positivity)
          have h2 : ((n : ℝ) - 1) * c ≤ n * t.val * c := by
            apply mul_le_mul_of_nonneg_right _ hc0; nlinarith
          have h3 : 0 ≤ c * n * t.val := by positivity
          nlinarith
