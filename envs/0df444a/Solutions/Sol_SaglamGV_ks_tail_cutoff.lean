-- Prove2me | solution 1 for SaglamGV.ks_tail_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-14T12:12:15.976604+00:00
-- url     : https://prove2.me/submissions/42999241-ec32-4f2f-8b09-32ee6232c789

import Definitions.Def_SelectiveDPT_H2

set_option autoImplicit false

private lemma entropy_bound (a u : ℝ) (ha : 0 < a) (ha2 : 2 * a ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    SelectiveDPT.H2 u ≤ 2 * a * Real.logb 2 (Real.exp 1 / a) := by
  have hmono : Real.binEntropy u ≤ Real.binEntropy (2 * a) :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨hu0, by norm_num; linarith⟩
      ⟨by positivity, by norm_num; linarith⟩ hu
  have hrest := Real.negMulLog_le_one_sub_self (show 0 ≤ 1 - 2 * a by linarith)
  have hlog := Real.log_le_log ha (show a ≤ 2 * a by linarith)
  have hent : Real.binEntropy u ≤ 2 * a * (1 - Real.log a) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * a by positivity)
    simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.negMulLog] at hmono hrest ⊢
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold SelectiveDPT.H2 Real.logb
  rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) ha.ne', Real.log_exp]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hent hlog2.le

private lemma rounding (n w : ℕ) (hn : 2 ≤ n) (hw : 0 < (w : ℝ))
    (hwn : (w : ℝ) ≤ n) :
    let a : ℝ := Real.logb 2 n / w
    let k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊
    a ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 2 * a := by
  dsimp only
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 1 ≤ Real.logb 2 n := by
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hnR
  have hc := Nat.le_ceil ((n : ℝ) * Real.logb 2 n / w)
  have hc' := (Nat.ceil_lt_add_one
    (show 0 ≤ (n : ℝ) * Real.logb 2 n / w by positivity)).le
  have hsmall : 1 / (n : ℝ) ≤ Real.logb 2 n / w := by
    apply (div_le_div_iff₀ hn0 hw).mpr
    nlinarith
  constructor
  · apply (le_div_iff₀ hn0).mpr
    convert hc using 1; ring
  · have hh := div_le_div_of_nonneg_right hc' hn0.le
    have he : ((n : ℝ) * Real.logb 2 n / w + 1) / n =
        Real.logb 2 n / w + 1 / n := by field_simp
    rw [he] at hh
    linarith

private lemma threshold (n w : ℕ) (u : ℝ) (hn : 2 ≤ n) (hw : 0 < (w : ℝ))
    (hu : Real.logb 2 n / w ≤ u) :
    Real.sqrt ((n : ℝ) + 1) * Real.exp (-2 * w * u) ≤ 1 / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogdom : Real.log n ≤ Real.logb 2 n := by
    unfold Real.logb
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  have hwu : Real.logb 2 n ≤ (w : ℝ) * u := by
    have hh := (div_le_iff₀ hw).mp hu
    nlinarith
  have hexp : Real.exp (-2 * w * u) ≤ 1 / (n : ℝ) ^ 2 := by
    calc
      _ ≤ Real.exp (-2 * Real.log n) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / (n : ℝ) ^ 2 := by
        rw [show -2 * Real.log n = -Real.log ((n : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring]
        rw [Real.exp_neg, Real.exp_log (pow_pos hn0 2)]
        simp
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ n :=
    (Real.sqrt_le_left hn0.le).mpr (by nlinarith)
  calc
    _ ≤ (n : ℝ) * (1 / (n : ℝ) ^ 2) :=
      mul_le_mul hsqrt hexp (by positivity) hn0.le
    _ = 1 / (n : ℝ) := by field_simp

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ n w : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ w →
        (w : ℝ) ≤ (1 / 2 - ε) * n →
        let k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊
        (k : ℝ) / n ≤ 1 / 2 -
            Real.sqrt (((w : ℝ) / n) * (1 - (w : ℝ) / n)) ∧
          Real.sqrt ((n : ℝ) + 1) * Real.exp (-2 * w * ((k : ℝ) / n)) ≤
            1 / (n : ℝ) ∧
          (n : ℝ) * (SelectiveDPT.H2 ((k : ℝ) / n) - 1) ≤
            -(n : ℝ) + 2 * n * Real.logb 2 n / w *
              Real.logb 2 (Real.exp 1 * w / Real.logb 2 n) := by
  by_cases hε2 : ε < 1 / 2
  · refine ⟨8 / ε ^ 2, by positivity, 2, le_rfl, ?_⟩
    intro n w hn hl hu
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by linarith)
    have hw0 : (0 : ℝ) < w := (mul_pos (by positivity) hlog).trans_le hl
    have hwn : (w : ℝ) ≤ n := by nlinarith
    let a : ℝ := Real.logb 2 n / w
    let k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊
    let u : ℝ := (k : ℝ) / n
    have ha0 : 0 < a := div_pos hlog hw0
    have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
    have heps' : ε ^ 2 < 1 / 4 := by nlinarith
    have hlarge : 8 * Real.logb 2 n ≤ (w : ℝ) * ε ^ 2 := by
      apply (div_le_iff₀ heps).mp
      simpa only [div_mul_eq_mul_div] using hl
    have ha : a ≤ ε ^ 2 / 8 := by
      apply (div_le_iff₀ hw0).mpr
      nlinarith
    have ha2 : 2 * a ≤ 1 / 2 := by nlinarith
    obtain ⟨hua, hu2a⟩ := rounding n w hn hw0 hwn
    change a ≤ u at hua
    change u ≤ 2 * a at hu2a
    have hp : 0 < (w : ℝ) / n := div_pos hw0 hn0
    have hpε : (w : ℝ) / n ≤ 1 / 2 - ε := (div_le_iff₀ hn0).mpr hu
    have hprod : ((w : ℝ) / n) * (1 - (w : ℝ) / n) ≤ 1 / 4 - ε ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - (w : ℝ) / n - ε by linarith)
        (show 0 ≤ 1 / 2 - (w : ℝ) / n + ε by linarith)]
    have hsqrt : Real.sqrt (((w : ℝ) / n) * (1 - (w : ℝ) / n)) ≤
        1 / 2 - ε ^ 2 := by
      apply (Real.sqrt_le_left (by linarith)).mpr
      nlinarith [sq_nonneg (ε ^ 2)]
    refine ⟨?_, threshold n w u hn hw0 hua, ?_⟩
    · change u ≤ _
      linarith
    · have hent := entropy_bound a u ha0 ha2 (le_trans ha0.le hua) hu2a
      have heq : Real.exp 1 / a = Real.exp 1 * w / Real.logb 2 n := by
        dsimp [a]
        field_simp
      change (n : ℝ) * (SelectiveDPT.H2 u - 1) ≤ _
      calc
        _ = -(n : ℝ) + n * SelectiveDPT.H2 u := by ring
        _ ≤ -(n : ℝ) + n * (2 * a * Real.logb 2 (Real.exp 1 / a)) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hent hn0.le) _
        _ = _ := by rw [heq]; dsimp [a]; ring
  · refine ⟨1, by norm_num, 2, le_rfl, ?_⟩
    intro n w hn hl hu
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by linarith)
    have hw0 : (0 : ℝ) < w := by linarith
    have hu0 : (1 / 2 - ε) * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
