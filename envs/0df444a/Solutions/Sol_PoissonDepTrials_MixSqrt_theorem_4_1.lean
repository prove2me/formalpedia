-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T23:20:00.535625+00:00
-- url     : https://prove2.me/submissions/d366b67a-e59e-4992-8bc8-3bb5a049791c

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory


theorem cs410_card_le (n m i : ℕ) :
    ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card ≤ 2 * m + 1 := by
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ))
    (s := (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m))
    (t := Finset.Icc ((i : ℤ) - m) ((i : ℤ) + m)) ?_ ?_
  · rw [Int.card_Icc] at h
    omega
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have := abs_le.mp hj.2
    constructor <;> linarith [this.1, this.2]
  · intro a _ b _ hab
    simpa using hab

theorem cs410_real (n m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m, f i * f j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
  set S : ℕ → Finset ℕ := fun i =>
    (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) with hS
  have hA : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hc : (S i).card ≤ 2 * m + 1 := cs410_card_le n m i
    exact_mod_cast hc
  have hB : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2
      = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2 := by
    simp only [hS, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_sub_comm]
  have hpt : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j
      ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    nlinarith [sq_nonneg (f i - f j)]
  have hsplit : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2
      = (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
         + ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  show ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j ≤ _
  linarith [hpt, hsplit, hA, hB]


namespace A03F915D

open PoissonDepTrials.MixSqrt

theorem aux (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by
  have hl0 : lam ≠ 0 := hlam.ne'
  refine ⟨?_, ?_⟩
  · intro w
    cases w with
    | zero =>
      simp only [stein, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, pow_zero,
        zero_add, Nat.zero_sub, CharP.cast_eq_zero, zero_mul, pow_one, div_one, mul_one, one_mul]
      field_simp
      ring
    | succ n =>
      simp only [stein, Nat.add_sub_cancel, Finset.sum_range_succ (n := n + 1)]
      rw [Nat.factorial_succ n]
      push_cast
      generalize (∑ k ∈ Finset.range (n + 1), (h k - poissonExp lam h) * lam ^ k /
        (k.factorial : ℝ)) = S
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      rw [pow_succ lam (n + 1)]
      field_simp
      ring
  · intro w _
    have hE : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp lam
    have hnn : ∀ k : ℕ, 0 ≤ lam ^ k / (k.factorial : ℝ) := fun k => by positivity
    have hs : Summable (fun k : ℕ => h k * (lam ^ k / (k.factorial : ℝ))) := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        (hE.summable.mul_left M))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn k)]
      exact mul_le_mul_of_nonneg_right (hM k) (hnn k)
    have hP : poissonExp lam h = Real.exp (-lam) * ∑' k : ℕ, h k * (lam ^ k / (k.factorial : ℝ)) := by
      rw [poissonExp, ← tsum_mul_left]
      congr 1
      ext k
      ring
    have hA : HasSum (fun k : ℕ => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) 0 := by
      have h1 := hs.hasSum.sub (hE.mul_left (poissonExp lam h))
      have h0 : (∑' k : ℕ, h k * (lam ^ k / (k.factorial : ℝ))) - poissonExp lam h * Real.exp lam = 0 := by
        rw [hP, Real.exp_neg]
        field_simp
        ring
      rw [h0] at h1
      have hfun : (fun k : ℕ => (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) =
          fun k => h k * (lam ^ k / (k.factorial : ℝ)) - poissonExp lam h * (lam ^ k / (k.factorial : ℝ)) := by
        funext k
        ring
      rw [hfun]
      exact h1
    have hT := (hasSum_nat_add_iff' w).mpr hA
    rw [hT.tsum_eq]
    simp only [stein]
    ring

/-- `|𝒫_λ h| ≤ M`. -/
theorem abs_poissonExp_le (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) : |poissonExp lam h| ≤ M := by
  have hE : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp lam
  have hB : HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * M)
      (Real.exp (-lam) * Real.exp lam * M) := by
    have := (hE.mul_left (Real.exp (-lam))).mul_right M
    have hfun : (fun k : ℕ => Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * M) =
        fun i : ℕ => Real.exp (-lam) * (lam ^ i / (i.factorial : ℝ)) * M := by
      funext k
      ring
    rw [hfun]
    exact this
  have hval : Real.exp (-lam) * Real.exp lam * M = M := by
    rw [← Real.exp_add]; simp
  rw [hval] at hB
  rw [poissonExp, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hB (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hnn : 0 ≤ Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) := by positivity
  rw [abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left (hM k) hnn

/-- Head bound by the recurrence. -/
theorem head_bound (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hg : ∀ k, |h k - poissonExp lam h| ≤ 2 * M)
    (hrec : ∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) :
    ∀ n : ℕ, (n : ℝ) < lam → |stein lam h (n + 1)| ≤ 2 * M / (lam - n) := by
  intro n
  induction n with
  | zero =>
    intro _
    have r := hrec 0
    simp only [Nat.cast_zero, zero_mul, zero_sub, zero_add] at r
    simp only [Nat.cast_zero, sub_zero, zero_add]
    rw [le_div_iff₀ hlam]
    have : |stein lam h 1| * lam = |h 0 - poissonExp lam h| := by
      rw [← r, abs_neg, abs_mul, abs_of_pos hlam, mul_comm]
    rw [this]
    exact hg 0
  | succ n ih =>
    intro hn
    push_cast at hn
    have hn' : (n : ℝ) < lam := by linarith
    have ha := ih hn'
    have hpos : 0 < lam - n := by linarith
    rw [le_div_iff₀ hpos] at ha
    have r := hrec (n + 1)
    push_cast at r
    have hb : lam * |stein lam h (n + 1 + 1)| ≤ ((n : ℝ) + 1) * |stein lam h (n + 1)| + 2 * M := by
      have e : lam * stein lam h (n + 1 + 1) =
          ((n : ℝ) + 1) * stein lam h (n + 1) - (h (n + 1) - poissonExp lam h) := by linarith
      have : |lam * stein lam h (n + 1 + 1)| ≤ ((n : ℝ) + 1) * |stein lam h (n + 1)| + 2 * M := by
        rw [e]
        calc |((n : ℝ) + 1) * stein lam h (n + 1) - (h (n + 1) - poissonExp lam h)|
            ≤ |((n : ℝ) + 1) * stein lam h (n + 1)| + |h (n + 1) - poissonExp lam h| :=
              abs_sub _ _
          _ ≤ ((n : ℝ) + 1) * |stein lam h (n + 1)| + 2 * M := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
              linarith [hg (n + 1)]
      rwa [abs_mul, abs_of_pos hlam] at this
    have hpos2 : 0 < lam - (n + 1) := by linarith
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
    rw [le_div_iff₀ hpos2]
    set a := |stein lam h (n + 1)| with ha_def
    set b := |stein lam h (n + 1 + 1)| with hb_def
    have ha0 : 0 ≤ a := abs_nonneg _
    have hb0 : 0 ≤ b := abs_nonneg _
    have h1 : lam * b * (lam - n) ≤ 2 * M * (lam + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hb hpos.le,
        mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    by_contra hc
    have hc := not_le.mp hc
    have hlp : 0 < lam * (lam - n) := mul_pos hlam hpos
    nlinarith [mul_lt_mul_of_pos_left hc hlp, mul_le_mul_of_nonneg_right h1 hpos2.le,
      mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]

/-- Tail bound via the tail series. -/
theorem tail_bound (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hg : ∀ k, |h k - poissonExp lam h| ≤ 2 * M)
    (htail : ∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ))
    (n : ℕ) (hn : lam < (n : ℝ) + 2) :
    |stein lam h (n + 1)| ≤ 2 * M * (((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam))) := by
  have e := htail (n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at e
  rw [e, ← tsum_mul_left]
  have hr0 : 0 ≤ lam / ((n : ℝ) + 2) := by positivity
  have hr1 : lam / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; exact hn
  have hG := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * M / ((n : ℝ) + 1))
  have hval : 2 * M / ((n : ℝ) + 1) * (1 - lam / ((n : ℝ) + 2))⁻¹ =
      2 * M * (((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam))) := by
    have h2 : (n : ℝ) + 2 - lam ≠ 0 := by linarith
    have h3 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h4 : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [one_sub_div h3]
    field_simp
  rw [hval] at hG
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hG (fun k => ?_)
  rw [Real.norm_eq_abs]
  have hfac : ((n + 1).factorial : ℝ) * ((n : ℝ) + 2) ^ k ≤ ((k + (n + 1)).factorial : ℝ) := by
    have := Nat.factorial_mul_pow_le_factorial (m := n + 1) (n := k)
    rw [show n + 1 + k = k + (n + 1) by ring] at this
    exact_mod_cast this
  have hnf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hkey : (n.factorial : ℝ) * (lam ^ (n + 1))⁻¹ *
      ((h (k + (n + 1)) - poissonExp lam h) * lam ^ (k + (n + 1)) /
        ((k + (n + 1)).factorial : ℝ)) =
      (h (k + (n + 1)) - poissonExp lam h) *
        ((n.factorial : ℝ) * lam ^ k / ((k + (n + 1)).factorial : ℝ)) := by
    rw [show lam ^ (k + (n + 1)) = lam ^ k * lam ^ (n + 1) from pow_add _ _ _]
    have : lam ^ (n + 1) ≠ 0 := by positivity
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) * lam ^ k /
    ((k + (n + 1)).factorial : ℝ) by positivity)]
  have hq : (n.factorial : ℝ) * lam ^ k / ((k + (n + 1)).factorial : ℝ) ≤
      1 / ((n : ℝ) + 1) * (lam / ((n : ℝ) + 2)) ^ k := by
    have hden : (0 : ℝ) < ((n + 1).factorial : ℝ) * ((n : ℝ) + 2) ^ k := by positivity
    calc (n.factorial : ℝ) * lam ^ k / ((k + (n + 1)).factorial : ℝ)
        ≤ (n.factorial : ℝ) * lam ^ k / (((n + 1).factorial : ℝ) * ((n : ℝ) + 2) ^ k) :=
          div_le_div_of_nonneg_left (by positivity) hden hfac
      _ = 1 / ((n : ℝ) + 1) * (lam / ((n : ℝ) + 2)) ^ k := by
          rw [Nat.factorial_succ]
          push_cast
          rw [div_pow]
          field_simp
  calc |h (k + (n + 1)) - poissonExp lam h| *
        ((n.factorial : ℝ) * lam ^ k / ((k + (n + 1)).factorial : ℝ))
      ≤ 2 * M * (1 / ((n : ℝ) + 1) * (lam / ((n : ℝ) + 2)) ^ k) :=
        mul_le_mul (hg _) hq (by positivity) (by positivity)
    _ = 2 * M / ((n : ℝ) + 1) * (lam / ((n : ℝ) + 2)) ^ k := by ring

open PoissonDepTrials.MixSqrt in
theorem lemma_3_4 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤ 6 * M * min (1 / Real.sqrt lam) 1 := by
  intro w hw
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  obtain ⟨hrec, htail⟩ := aux lam hlam h M hM
  have hP := abs_poissonExp_le lam hlam h M hM
  have hg : ∀ k, |h k - poissonExp lam h| ≤ 2 * M := fun k => by
    calc |h k - poissonExp lam h| ≤ |h k| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM k]
  have hT := tail_bound lam hlam h M hM0 hg htail
  have hH := head_bound lam hlam h M hM0 hg hrec
  simp only [delta]
  rcases lt_or_ge lam 1 with hl1 | hl1
  · -- small λ: min = 1
    have hs : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr hl1.le
    have hspos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    rw [min_eq_right (one_le_one_div hspos hs), mul_one]
    have t1 := hT n (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have t2 := hT (n + 1) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; push_cast; linarith)
    push_cast at t2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have q1 : ((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam)) ≤ 2 := by
      rw [div_le_iff₀ (by apply mul_pos <;> linarith)]
      nlinarith
    have q2 : ((n : ℝ) + 1 + 2) / (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2 - lam)) ≤ 1 := by
      rw [div_le_iff₀ (by apply mul_pos <;> linarith)]
      nlinarith
    have b1 := le_trans t1 (mul_le_mul_of_nonneg_left q1 (by positivity))
    have b2 := le_trans t2 (mul_le_mul_of_nonneg_left q2 (by positivity))
    rw [show n + 1 + 1 = n + 1 + 1 from rfl] at b2
    calc |stein lam h (n + 1 + 1) - stein lam h (n + 1)|
        ≤ |stein lam h (n + 1 + 1)| + |stein lam h (n + 1)| := abs_sub _ _
      _ ≤ 6 * M := by linarith
  · -- large λ: min = 1/√λ
    have hs1 : 1 ≤ Real.sqrt lam := Real.one_le_sqrt.mpr hl1
    have hspos : 0 < Real.sqrt lam := by linarith
    rw [min_eq_left ((div_le_one hspos).mpr hs1)]
    have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
    have hsle : Real.sqrt lam ≤ lam := by nlinarith
    have r := hrec (n + 1)
    push_cast at r
    have e : lam * (stein lam h (n + 1 + 1) - stein lam h (n + 1)) =
        ((n : ℝ) + 1 - lam) * stein lam h (n + 1) - (h (n + 1) - poissonExp lam h) := by
      linarith
    have key : |((n : ℝ) + 1 - lam)| * |stein lam h (n + 1)| ≤ 4 * M := by
      rcases le_or_gt lam ((n : ℝ) + 1) with hc | hc
      · have t := hT n (by linarith)
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1 - lam)]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have q : ((n : ℝ) + 1 - lam) * (((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam)))
            ≤ 2 := by
          rw [← mul_div_assoc, div_le_iff₀ (by apply mul_pos <;> linarith)]
          nlinarith
        calc ((n : ℝ) + 1 - lam) * |stein lam h (n + 1)|
            ≤ ((n : ℝ) + 1 - lam) *
                (2 * M * (((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam)))) :=
              mul_le_mul_of_nonneg_left t (by linarith)
          _ = 2 * M * (((n : ℝ) + 1 - lam) *
                (((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2 - lam)))) := by ring
          _ ≤ 2 * M * 2 := mul_le_mul_of_nonneg_left q (by positivity)
          _ = 4 * M := by ring
      · have t := hH n (by linarith)
        rw [abs_of_neg (by linarith : (n : ℝ) + 1 - lam < 0)]
        have hpos : 0 < lam - n := by linarith
        rw [le_div_iff₀ hpos] at t
        nlinarith [abs_nonneg (stein lam h (n + 1))]
    have hb : lam * |stein lam h (n + 1 + 1) - stein lam h (n + 1)| ≤ 6 * M := by
      have : |lam * (stein lam h (n + 1 + 1) - stein lam h (n + 1))| ≤ 6 * M := by
        rw [e]
        calc |((n : ℝ) + 1 - lam) * stein lam h (n + 1) - (h (n + 1) - poissonExp lam h)|
            ≤ |((n : ℝ) + 1 - lam) * stein lam h (n + 1)| + |h (n + 1) - poissonExp lam h| :=
              abs_sub _ _
          _ ≤ 6 * M := by rw [abs_mul]; linarith [hg (n + 1)]
      rwa [abs_mul, abs_of_pos hlam] at this
    rw [show 6 * M * (1 / Real.sqrt lam) = 6 * M / Real.sqrt lam by ring]
    rw [le_div_iff₀ hspos]
    have h0 := abs_nonneg (stein lam h (n + 1 + 1) - stein lam h (n + 1))
    nlinarith [mul_le_mul_of_nonneg_left hsle h0]

end A03F915D
namespace T41

open PoissonDepTrials.MixSqrt

theorem measurable_X_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    Measurable (fun ω => (X i ω : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hX.1 i)

theorem X_le_one_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    ∀ᵐ ω ∂P, (X i ω : ℝ) ≤ 1 := by
  filter_upwards [hX.2.2 i] with ω hω
  exact_mod_cast hω

theorem integrable_X {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    Integrable (fun ω => (X i ω : ℝ)) P := by
  refine Integrable.of_bound (measurable_X_real hX i).aestronglyMeasurable 1 ?_
  filter_upwards [X_le_one_real hX i] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hω

theorem integrable_XX {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i j : ℕ) :
    Integrable (fun ω => (X i ω : ℝ) * X j ω) P := by
  refine Integrable.of_bound
    ((measurable_X_real hX i).mul (measurable_X_real hX j)).aestronglyMeasurable 1 ?_
  filter_upwards [X_le_one_real hX i, X_le_one_real hX j] with ω hi hj
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : (0 : ℝ) ≤ X j ω := Nat.cast_nonneg _
  nlinarith

theorem integral_X_eq_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (j : ℕ) :
    ∫ ω, (X j ω : ℝ) ∂P = prob P X j := by
  have hms : MeasurableSet {ω | X j ω = 1} := (hX.1 j) (measurableSet_singleton 1)
  have hae : (fun ω => (X j ω : ℝ)) =ᵐ[P] {ω | X j ω = 1}.indicator 1 := by
    filter_upwards [hX.2.2 j] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [integral_congr_ae hae, integral_indicator_one hms]
  rfl

theorem prob_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ) (i : ℕ) :
    0 ≤ prob P X i := measureReal_nonneg

/-- `|∫ F · Δf(G+1)| ≤ 6μ ∫ F` for `F ≥ 0` integrable. -/
theorem abs_integral_mul_delta_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (hF0 : ∀ ω, 0 ≤ F ω) (hF : Integrable F P) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ w : ℕ, 1 ≤ w → |g w| ≤ C) (G : Ω → ℕ) :
    |∫ ω, F ω * g (G ω + 1) ∂P| ≤ C * ∫ ω, F ω ∂P := by
  rw [← integral_const_mul]
  have := norm_integral_le_of_norm_le (hF.const_mul C) (μ := P)
    (f := fun ω => F ω * g (G ω + 1)) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF0 ω), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hg _ (by omega)) (hF0 ω))
  rwa [Real.norm_eq_abs] at this

end T41

namespace T41

open PoissonDepTrials.MixSqrt

theorem sum_range_sub_mul_two (n : ℕ) : (∑ k ∈ Finset.range n, (n - k)) * 2 = n * (n + 1) := by
  have h1 : ∑ k ∈ Finset.range n, (n - k) = ∑ k ∈ Finset.range n, (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => k + 1) n]
    exact Finset.sum_congr rfl fun k hk => by have := Finset.mem_range.mp hk; omega
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, add_mul,
    Finset.sum_range_id_mul_two]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

/-- A sequence with values in `[0, 1/x]` (`x ≥ 1`) and first moment `≤ 1` has mass `≤ 2/√x`. -/
theorem sum_le_of_moment (x : ℝ) (hx : 1 ≤ x) (N : ℕ) (v : ℕ → ℝ) (hv0 : ∀ k, 0 ≤ v k)
    (hv1 : ∀ k, v k ≤ 1 / x) (hm : ∑ k ∈ Finset.range N, (k : ℝ) * v k ≤ 1) :
    ∑ k ∈ Finset.range N, v k ≤ 2 / Real.sqrt x := by
  set r := Real.sqrt x with hr
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr hx
  have hx0 : 0 < x := by linarith
  have hrx : r * r = x := Real.mul_self_sqrt hx0.le
  set n := ⌊r⌋₊ + 1 with hn
  have hn1 : r < (n : ℝ) := by rw [hn]; push_cast; exact Nat.lt_floor_add_one r
  have hn2 : (n : ℝ) ≤ r + 1 := by
    rw [hn]; push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ r)]
  have hpt : ∀ k, (n : ℝ) * v k ≤ (k : ℝ) * v k + ((n - k : ℕ) : ℝ) / x := by
    intro k
    rcases le_or_gt k n with hk | hk
    · have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      rw [Nat.cast_sub hk]
      have h1 := mul_le_mul_of_nonneg_left (hv1 k) (sub_nonneg.mpr hk')
      have h2 : ((n : ℝ) - k) * (1 / x) = ((n : ℝ) - k) / x := by ring
      nlinarith
    · rw [Nat.sub_eq_zero_of_le hk.le]
      have hk' : (n : ℝ) ≤ k := by exact_mod_cast hk.le
      simp only [Nat.cast_zero, zero_div, add_zero]
      exact mul_le_mul_of_nonneg_right hk' (hv0 k)
  set B := ∑ k ∈ Finset.range N, v k with hB
  have h1 : (n : ℝ) * B ≤ ∑ k ∈ Finset.range N, (k : ℝ) * v k
      + (∑ k ∈ Finset.range N, ((n - k : ℕ) : ℝ)) / x := by
    rw [hB, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hpt k
  have h2 : (∑ k ∈ Finset.range N, ((n - k : ℕ) : ℝ)) ≤ n * (n + 1) / 2 := by
    rw [← Nat.cast_sum]
    have h3 : ∑ k ∈ Finset.range N, (n - k) ≤ ∑ k ∈ Finset.range n, (n - k) :=
      Finset.sum_le_sum_of_ne_zero fun k _ hk => Finset.mem_range.mpr (by omega)
    have h4 := sum_range_sub_mul_two n
    have h5 : ((∑ k ∈ Finset.range N, (n - k) : ℕ) : ℝ) * 2 ≤ n * (n + 1) := by
      exact_mod_cast (Nat.mul_le_mul_right 2 h3).trans h4.le
    linarith
  have hnB : (n : ℝ) * B ≤ 1 + n * (n + 1) / 2 / x := by
    have : (∑ k ∈ Finset.range N, ((n - k : ℕ) : ℝ)) / x ≤ n * (n + 1) / 2 / x :=
      div_le_div_of_nonneg_right h2 hx0.le
    linarith
  have key : 2 * r * r + n * (n + 1) ≤ 4 * n * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (by linarith : (0 : ℝ) ≤ r),
      mul_nonneg (sub_nonneg.mpr hn1.le) (by linarith : (0 : ℝ) ≤ 3 * r - n - 1)]
  have h6 : (n : ℝ) * B * (r * r) ≤ r * r + n * (n + 1) / 2 := by
    have := mul_le_mul_of_nonneg_right hnB (by positivity : (0 : ℝ) ≤ r * r)
    have e : (1 + n * (n + 1) / 2 / x) * (r * r) = r * r + n * (n + 1) / 2 := by
      rw [hrx]; field_simp
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have h7 : (n : ℝ) * r * (B * r) ≤ (n * r) * 2 := by nlinarith
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < r)]
  exact le_of_mul_le_mul_left h7 (by positivity)

/-- Chen (1975), Lemma 3.1. -/
theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hl1 : 1 ≤ lam := le_trans hw1 hlw
  have hl0 : 0 < lam := by linarith
  set v : ℕ → ℝ := fun j => ((w - 1).descFactorial j : ℝ) / lam ^ (j + 1) with hv
  have hrep : ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      = ∑ j ∈ Finset.range w, v j := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [hv]
    have hf := Nat.factorial_mul_descFactorial (show j ≤ w - 1 by omega)
    have hp : lam ^ (w - 1 - j) * lam ^ (j + 1) = lam ^ w := by
      rw [← pow_add]; congr 1; omega
    rw [← hf, ← hp]
    push_cast
    have : (((w - 1 - j).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hrep]
  have hv0 : ∀ j, 0 ≤ v j := fun j => by simp only [hv]; positivity
  have hvz : v 0 = 1 / lam := by simp [hv, Nat.descFactorial_zero]
  have hrec : ∀ j, lam * v (j + 1) = (((w - 1 - j : ℕ)) : ℝ) * v j := by
    intro j
    simp only [hv]
    rw [Nat.descFactorial_succ, pow_succ lam (j + 1)]
    push_cast
    field_simp
  clear_value v
  have hc : ∀ j, (((w - 1 - j : ℕ)) : ℝ) ≤ lam := by
    intro j
    have : (w - 1 - j : ℕ) ≤ w := by omega
    have : (((w - 1 - j : ℕ)) : ℝ) ≤ w := by exact_mod_cast this
    linarith
  have hdec : ∀ j, v (j + 1) ≤ v j := by
    intro j
    have h1 := hrec j
    have h2 := mul_le_mul_of_nonneg_right (hc j) (hv0 j)
    nlinarith [hv0 j, hv0 (j + 1)]
  have hv1 : ∀ j, v j ≤ 1 / lam := by
    intro j
    induction j with
    | zero => rw [hvz]
    | succ j ih => exact (hdec j).trans ih
  have hid : ∀ N, N ≤ w → lam * ∑ j ∈ Finset.range (N + 1), v j - 1
      = ((w : ℝ) - 1) * ∑ j ∈ Finset.range N, v j - ∑ j ∈ Finset.range N, (j : ℝ) * v j := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [zero_add, Finset.sum_range_one, Finset.sum_range_zero, mul_zero, sub_zero, hvz,
        mul_one_div_cancel hl0.ne', sub_self]
    | succ N ih =>
      intro hN
      have ih' := ih (by omega)
      rw [Finset.sum_range_succ (fun j => v j) N] at ih'
      rw [Finset.sum_range_succ (fun j => v j) (N + 1), Finset.sum_range_succ (fun j => v j) N,
        Finset.sum_range_succ (fun j => (j : ℝ) * v j) N]
      have hr := hrec N
      rw [Nat.cast_sub (by omega : N ≤ w - 1), Nat.cast_sub (by omega : 1 ≤ w)] at hr
      push_cast at hr
      linear_combination ih' + hr
  have hm : ∑ j ∈ Finset.range w, (j : ℝ) * v j ≤ 1 := by
    have e := hid w le_rfl
    rw [Finset.sum_range_succ (fun j => v j) w] at e
    have hB0 : 0 ≤ ∑ j ∈ Finset.range w, v j := Finset.sum_nonneg fun j _ => hv0 j
    have : ((w : ℝ) - 1 - lam) * ∑ j ∈ Finset.range w, v j ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hB0
    nlinarith [mul_nonneg hl0.le (hv0 w)]
  exact sum_le_of_moment lam hl1 w v hv0 hv1 hm

/-- Chen (1975), Lemma 3.2. -/
theorem lemma_3_2 (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  set v : ℕ → ℝ := fun k => ((w - 1).factorial : ℝ) * lam ^ k / ((k + w).factorial : ℝ) with hv
  have hterm : ∀ k : ℕ, ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      (lam ^ (k + w) / ((k + w).factorial : ℝ)) = v k := by
    intro k
    simp only [hv]
    rw [pow_add]
    have : lam ^ w ≠ 0 := by positivity
    field_simp
  rw [← tsum_mul_left]
  simp_rw [hterm]
  have hv0 : ∀ k, 0 ≤ v k := fun k => by simp only [hv]; positivity
  have hrec : ∀ k : ℕ, ((w : ℝ) + k + 1) * v (k + 1) = lam * v k := by
    intro k
    simp only [hv]
    rw [show k + 1 + w = (k + w) + 1 by ring, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  have hvz : v 0 = 1 / w := by
    simp only [hv, pow_zero, zero_add, mul_one]
    obtain ⟨u, rfl⟩ : ∃ u, w = u + 1 := ⟨w - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  clear_value v
  have hdec : ∀ k, v (k + 1) ≤ v k := by
    intro k
    have h1 := hrec k
    have h2 := mul_le_mul_of_nonneg_right hlw (hv0 k)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [hv0 k, hv0 (k + 1)]
  have hv1 : ∀ k, v k ≤ 1 / w := by
    intro k
    induction k with
    | zero => rw [hvz]
    | succ k ih => exact (hdec k).trans ih
  have hid : ∀ N, ∑ k ∈ Finset.range (N + 1), (k : ℝ) * v k
      + w * ∑ k ∈ Finset.range (N + 1), v k = 1 + lam * ∑ k ∈ Finset.range N, v k := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, zero_mul, Finset.range_zero,
        Finset.sum_empty, mul_zero, add_zero, hvz]
      field_simp
    | succ N ih =>
      rw [Finset.sum_range_succ (fun k => (k : ℝ) * v k) (N + 1),
        Finset.sum_range_succ (fun k => v k) (N + 1), Finset.sum_range_succ (fun k => v k) N]
      have hr := hrec N
      rw [Finset.sum_range_succ (fun k => v k) N] at ih
      push_cast
      linear_combination ih + hr
  have hm : ∀ N, ∑ k ∈ Finset.range N, (k : ℝ) * v k ≤ 1 := by
    intro N
    rcases N with _ | N
    · simp
    · have e := hid N
      rw [Finset.sum_range_succ (fun k => v k) N] at e
      have hB0 : 0 ≤ ∑ k ∈ Finset.range N, v k := Finset.sum_nonneg fun k _ => hv0 k
      have := mul_le_mul_of_nonneg_right hlw hB0
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ w) (hv0 N)]
  exact Real.tsum_le_of_sum_range_le hv0 fun N => sum_le_of_moment w hw1 N v hv0 hv1 (hm N)

/-- Chen (1975), Lemma 3.3. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by
  intro w hw
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hP := A03F915D.abs_poissonExp_le lam hlam h M hM
  have hg : ∀ k, |h k - poissonExp lam h| ≤ 2 * M := fun k =>
    (abs_sub _ _).trans (by linarith [hM k])
  obtain ⟨_, htail⟩ := A03F915D.aux lam hlam h M hM
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hc0 : (0 : ℝ) ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ := by positivity
  rcases le_total (w : ℝ) lam with hwl | hlw
  · have hA := lemma_3_1 lam w hw hwl
    have hl1 : 1 ≤ lam := hw1.trans hwl
    have hs1 : 1 ≤ Real.sqrt lam := Real.one_le_sqrt.mpr hl1
    rw [min_eq_left ((div_le_one (by linarith)).mpr hs1)]
    have h1 : |stein lam h w| ≤ 2 * M * (((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
        ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)) := by
      simp only [stein, abs_neg]
      rw [abs_mul, abs_of_nonneg hc0]
      calc ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
            |∑ k ∈ Finset.range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)|
          ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
            ∑ k ∈ Finset.range w, 2 * M * (lam ^ k / (k.factorial : ℝ)) := by
            gcongr
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
            rw [mul_div_assoc, abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ k / (k.factorial : ℝ))]
            exact mul_le_mul_of_nonneg_right (hg k) (by positivity)
        _ = 2 * M * (((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
            ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)) := by
            rw [← Finset.mul_sum]; ring
    calc |stein lam h w| ≤ 2 * M * (2 / Real.sqrt lam) :=
          h1.trans (mul_le_mul_of_nonneg_left hA (by positivity))
      _ = 4 * M * (1 / Real.sqrt lam) := by ring
  · have hB := lemma_3_2 lam hlam w hw hlw
    have hsum : Summable (fun k : ℕ => lam ^ (k + w) / ((k + w).factorial : ℝ)) :=
      (summable_nat_add_iff w).mpr (Real.summable_pow_div_factorial lam)
    have e := htail w hw
    have hT : |∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)|
        ≤ 2 * M * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ) := by
      rw [← tsum_mul_left, ← Real.norm_eq_abs]
      refine tsum_of_norm_bounded (hsum.mul_left (2 * M)).hasSum fun k => ?_
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ (k + w) / ((k + w).factorial : ℝ))]
      exact mul_le_mul_of_nonneg_right (hg _) (by positivity)
    have h1 : |stein lam h w| ≤ 2 * M * (((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
        ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)) := by
      rw [e, abs_mul, abs_of_nonneg hc0]
      calc _ ≤ ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
            (2 * M * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)) := by gcongr
        _ = _ := by ring
    have hs0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hsw : Real.sqrt lam ≤ Real.sqrt w := Real.sqrt_le_sqrt hlw
    have hsw1 : 1 ≤ Real.sqrt w := Real.one_le_sqrt.mpr hw1
    have hq : 2 / Real.sqrt w ≤ 2 * min (1 / Real.sqrt lam) 1 := by
      rcases min_cases (1 / Real.sqrt lam) 1 with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
      · rw [show 2 * (1 / Real.sqrt lam) = 2 / Real.sqrt lam by ring]
        exact div_le_div_of_nonneg_left (by norm_num) hs0 hsw
      · rw [mul_one]
        exact div_le_self (by norm_num) hsw1
    calc |stein lam h w| ≤ 2 * M * (2 / Real.sqrt w) :=
          h1.trans (mul_le_mul_of_nonneg_left hB (by positivity))
      _ ≤ 2 * M * (2 * min (1 / Real.sqrt lam) 1) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 4 * M * min (1 / Real.sqrt lam) 1 := by ring

end T41
namespace T41

open PoissonDepTrials.MixSqrt

theorem sum_filter_step (s : Finset ℕ) (x : ℕ → ℕ) (Q Q' A : ℕ → Prop) [DecidablePred Q]
    [DecidablePred Q'] [DecidablePred A] (j : ℕ) (hQ : ∀ k, Q k ↔ (A k ∧ k ≤ j))
    (hQ' : ∀ k, Q' k ↔ (A k ∧ k < j)) :
    ∑ k ∈ s with Q k, x k = ∑ k ∈ s with Q' k, x k + (if j ∈ s ∧ A j then x j else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have e : ∀ k ∈ s, (if Q k then x k else 0)
      = (if Q' k then x k else 0) + (if j = k then (if A k then x k else 0) else 0) := by
    intro k _
    by_cases hk : j = k
    · subst hk
      have h1 : ¬ Q' j := fun h => lt_irrefl j ((hQ' j).mp h).2
      by_cases hA : A j
      · have h2 : Q j := (hQ j).mpr ⟨hA, le_rfl⟩
        simp [h1, h2, hA]
      · have h2 : ¬ Q j := fun h => hA ((hQ j).mp h).1
        simp [h1, h2, hA]
    · by_cases hq : Q k
      · have h2 : Q' k := (hQ' k).mpr ⟨((hQ k).mp hq).1,
          lt_of_le_of_ne ((hQ k).mp hq).2 (fun e => hk e.symm)⟩
        simp [hq, h2, hk]
      · have h2 : ¬ Q' k := fun h => hq ((hQ k).mpr ⟨((hQ' k).mp h).1, ((hQ' k).mp h).2.le⟩)
        simp [hq, h2, hk]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq]
  by_cases hj : j ∈ s <;> by_cases hA : A j <;> simp [hj, hA]

theorem telescope (g : ℕ → ℝ) (a c : ℕ → ℕ) (hc : ∀ j, c j ≤ 1)
    (ha : ∀ j, a (j + 1) = a j + c j) (T : ℕ) :
    g (a T + 1) - g (a 0 + 1) = ∑ j ∈ Finset.range T, (c j : ℝ) * delta g (a j + 1) := by
  rw [← Finset.sum_range_sub (fun j => g (a j + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha j]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hc j) with h | h
  · simp [h]
  · simp [h, delta]

theorem Y_step {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i j : ℕ) (ω : Ω) :
    Y n m X i (j : ℤ) ω = Y n m X i ((j : ℤ) - 1) ω
      + (if j ∈ Finset.Icc 1 n ∧ (i : ℤ) - m ≤ j then X j ω else 0) := by
  simp only [Y]
  rw [sum_filter_step (Finset.Icc 1 n) (fun k => X k ω)
    (fun k : ℕ => (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ (j : ℤ))
    (fun k : ℕ => (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ (j : ℤ) - 1)
    (fun k : ℕ => (i : ℤ) - m ≤ k) j (fun k => by omega) (fun k => by omega)]
  ring

theorem Y'_step {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i j : ℕ) (ω : Ω) :
    Y' n m X i (j : ℤ) ω = Y' n m X i ((j : ℤ) - 1) ω
      + (if j ∈ Finset.Icc 1 n ∧ (j ≠ i ∧ (i : ℤ) - m ≤ j) then X j ω else 0) := by
  simp only [Y']
  rw [sum_filter_step (Finset.Icc 1 n) (fun k => X k ω)
    (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ (j : ℤ))
    (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ (j : ℤ) - 1)
    (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k) j (fun k => by omega) (fun k => by omega)]
  ring

theorem Y_zero {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    Y n m X i (((0 : ℕ) : ℤ) - 1) ω = V n m X i ω := by
  simp only [Y]
  rw [Finset.sum_eq_zero, add_zero]
  intro k hk
  simp only [Finset.mem_filter] at hk
  exfalso; omega

theorem Y'_zero {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    Y' n m X i (((0 : ℕ) : ℤ) - 1) ω = V n m X i ω := by
  simp only [Y']
  rw [Finset.sum_eq_zero, add_zero]
  intro k hk
  simp only [Finset.mem_filter] at hk
  exfalso; omega

theorem W_split {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    W n X ω = V n m X i ω
      + ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => ¬ (m < Int.natAbs ((k : ℤ) - i))), X k ω := by
  simp only [W, V]
  rw [Finset.sum_filter_add_sum_filter_not]

theorem Y_top {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    Y n m X i (((i + m : ℕ) : ℤ)) ω = W n X ω := by
  rw [W_split n m X i ω]
  simp only [Y]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact Finset.filter_congr fun k _ => by push_cast; omega

theorem Y'_top {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (hi : i ∈ Finset.Icc 1 n)
    (ω : Ω) : Y' n m X i (((i + m : ℕ) : ℤ)) ω + X i ω = W n X ω := by
  rw [W_split n m X i ω]
  simp only [Y']
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun k : ℕ => ¬ (m < Int.natAbs ((k : ℤ) - i)))) (fun k => k ≠ i)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun k _ => by push_cast; omega
  · have : ((Finset.Icc 1 n).filter (fun k : ℕ => ¬ (m < Int.natAbs ((k : ℤ) - i)))).filter
        (fun k => ¬ k ≠ i) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc] at hi ⊢
      constructor
      · rintro ⟨_, h⟩; omega
      · rintro rfl; refine ⟨⟨hi, by omega⟩, by omega⟩
    rw [this, Finset.sum_singleton]

theorem pointwise_Y {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hb : ∀ k, X k ω ≤ 1)
    (g : ℕ → ℝ) (i : ℕ) :
    g (W n X ω + 1) = g (V n m X i ω + 1) + ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        (X j ω : ℝ) * delta g (Y n m X i ((j : ℤ) - 1) ω + 1) := by
  set c : ℕ → ℕ := fun j => if j ∈ Finset.Icc 1 n ∧ (i : ℤ) - m ≤ j then X j ω else 0 with hc
  have hc1 : ∀ j, c j ≤ 1 := fun j => by
    simp only [hc]; split_ifs
    · exact hb j
    · exact zero_le_one
  have ha : ∀ j, Y n m X i (((j + 1 : ℕ) : ℤ) - 1) ω = Y n m X i ((j : ℤ) - 1) ω + c j := by
    intro j
    rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by push_cast; ring]
    exact Y_step n m X i j ω
  have ht := telescope g (fun j => Y n m X i ((j : ℤ) - 1) ω) c hc1 ha (i + m + 1)
  rw [show (((i + m + 1 : ℕ) : ℤ) - 1) = ((i + m : ℕ) : ℤ) by push_cast; ring, Y_top,
    Y_zero] at ht
  rw [← sub_eq_iff_eq_add', ht]
  simp only [hc, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, abs_le]
  omega

theorem pointwise_Y' {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hb : ∀ k, X k ω ≤ 1)
    (g : ℕ → ℝ) (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
    (X i ω : ℝ) * g (W n X ω) = (X i ω : ℝ) * g (V n m X i ω + 1)
      + ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        (X i ω : ℝ) * X j ω * delta g (Y' n m X i ((j : ℤ) - 1) ω + 1) := by
  set c : ℕ → ℕ := fun j =>
    if j ∈ Finset.Icc 1 n ∧ (j ≠ i ∧ (i : ℤ) - m ≤ j) then X j ω else 0 with hc
  have hc1 : ∀ j, c j ≤ 1 := fun j => by
    simp only [hc]; split_ifs
    · exact hb j
    · exact zero_le_one
  have ha : ∀ j, Y' n m X i (((j + 1 : ℕ) : ℤ) - 1) ω = Y' n m X i ((j : ℤ) - 1) ω + c j := by
    intro j
    rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by push_cast; ring]
    exact Y'_step n m X i j ω
  have ht := telescope g (fun j => Y' n m X i ((j : ℤ) - 1) ω) c hc1 ha (i + m + 1)
  rw [show (((i + m + 1 : ℕ) : ℤ) - 1) = ((i + m : ℕ) : ℤ) by push_cast; ring,
    Y'_zero] at ht
  have hW := Y'_top n m X i hi ω
  have hmain : (X i ω : ℝ) * g (W n X ω) = (X i ω : ℝ) * g (Y' n m X i ((i + m : ℕ) : ℤ) ω + 1) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hb i) with h0 | h1
    · simp [h0]
    · rw [h1] at hW; rw [← hW]
  rw [hmain, ← sub_eq_iff_eq_add', ← mul_sub, ht, Finset.mul_sum]
  simp only [hc, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => by ring)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, abs_le, abs_pos]
  omega

theorem pointwise_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) (m : ℕ) (h : ℕ → ℝ) (f : ℕ → ℝ)
    (hstein : ∀ w : ℕ, (w : ℝ) * f w - lam P n X * f (w + 1) = h w - poissonExp (lam P n X) h)
    (ω : Ω) (hb : ∀ k, X k ω ≤ 1) :
    h (W n X ω) = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1))
      + (∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1))
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) := by
  have hs := hstein (W n X ω)
  have hW : ((W n X ω : ℕ) : ℝ) = ∑ i ∈ Finset.Icc 1 n, (X i ω : ℝ) := by simp [W]
  have e1 : ((W n X ω : ℕ) : ℝ) * f (W n X ω) = ∑ i ∈ Finset.Icc 1 n,
      ((X i ω : ℝ) * f (V n m X i ω + 1) + ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) := by
    rw [hW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => pointwise_Y' n m X ω hb f i hi
  have e2 : lam P n X * f (W n X ω + 1) = ∑ i ∈ Finset.Icc 1 n,
      (prob P X i * f (V n m X i ω + 1) + ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1))) := by
    rw [show lam P n X = ∑ i ∈ Finset.Icc 1 n, prob P X i from rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pointwise_Y n m X ω hb f i, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib] at e1 e2
  have e3 : ∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1)
      = ∑ i ∈ Finset.Icc 1 n, (X i ω : ℝ) * f (V n m X i ω + 1)
        - ∑ i ∈ Finset.Icc 1 n, prob P X i * f (V n m X i ω + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  linarith

theorem meas_sum {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℕ} (hXm : ∀ i, Measurable (X i))
    (s : Finset ℕ) : Measurable (fun ω => ∑ k ∈ s, X k ω) :=
  Finset.measurable_sum s fun k _ => hXm k

theorem meas_V {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℕ} (hXm : ∀ i, Measurable (X i))
    (n m i : ℕ) : Measurable (V n m X i) := meas_sum hXm _

theorem meas_Y {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℕ} (hXm : ∀ i, Measurable (X i))
    (n m i : ℕ) (t : ℤ) : Measurable (Y n m X i t) :=
  (meas_V hXm n m i).add (meas_sum hXm _)

theorem meas_Y' {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℕ} (hXm : ∀ i, Measurable (X i))
    (n m i : ℕ) (t : ℤ) : Measurable (Y' n m X i t) :=
  (meas_V hXm n m i).add (meas_sum hXm _)

theorem integrable_of_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ} (hF : Measurable F) (K : ℝ) (hK : ∀ᵐ ω ∂P, |F ω| ≤ K) : Integrable F P :=
  Integrable.of_bound hF.aestronglyMeasurable K (by simpa [Real.norm_eq_abs] using hK)

theorem identity_2_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hlam : 0 < lam P n X) (m : ℕ) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta (stein (lam P n X) h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein (lam P n X) h (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein (lam P n X) h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  obtain ⟨hrec, _⟩ := A03F915D.aux (lam P n X) hlam h M hM
  set f := stein (lam P n X) h with hf
  set Cf := 4 * M * min (1 / Real.sqrt (lam P n X)) 1 with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  have hfb : ∀ k, |f k| ≤ Cf := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [hf, stein, Finset.range_zero, Finset.sum_empty, mul_zero, neg_zero, abs_zero]
      exact hCf0
    · exact lemma_3_3 (lam P n X) hlam h M hM k hk
  have hdb : ∀ k, |delta f k| ≤ 2 * Cf := fun k => by
    simp only [delta]
    exact (abs_sub _ _).trans (by linarith [hfb k, hfb (k + 1)])
  have hb : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX.2.2
  have hXr : ∀ i ω, X i ω ≤ 1 → |(X i ω : ℝ)| ≤ 1 := fun i ω hω => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hω
  have hpt : (fun ω => h (W n X ω)) =ᵐ[P] fun ω => poissonExp (lam P n X) h
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1))
      + (∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1))
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) :=
    hb.mono fun ω hω => pointwise_identity P n X m h f hrec ω hω
  have iA : ∀ i j, Integrable (fun ω => (X i ω : ℝ) * X j ω
      * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) P := by
    intro i j
    refine integrable_of_bdd (((measurable_X_real hX i).mul (measurable_X_real hX j)).mul
      ((measurable_of_countable (fun k => delta f (k + 1))).comp (meas_Y' hX.1 n m i _)))
      (1 * 1 * (2 * Cf)) ?_
    filter_upwards [hb] with ω hω
    rw [abs_mul, abs_mul]
    have h1 := hXr i ω (hω i)
    have h2 := hXr j ω (hω j)
    have h3 := hdb (Y' n m X i ((j : ℤ) - 1) ω + 1)
    gcongr
  have iB : ∀ i, Integrable (fun ω => ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1)) P := by
    intro i
    refine integrable_of_bdd (((measurable_X_real hX i).sub_const _).mul
      ((measurable_of_countable (fun k => f (k + 1))).comp (meas_V hX.1 n m i)))
      ((1 + |prob P X i|) * Cf) ?_
    filter_upwards [hb] with ω hω
    rw [abs_mul]
    have h1 := hXr i ω (hω i)
    have h2 := hfb (V n m X i ω + 1)
    have h3 : |(X i ω : ℝ) - prob P X i| ≤ 1 + |prob P X i| := (abs_sub _ _).trans (by linarith)
    gcongr
  have iC : ∀ i j, Integrable (fun ω => prob P X i * ((X j ω : ℝ)
      * delta f (Y n m X i ((j : ℤ) - 1) ω + 1))) P := by
    intro i j
    refine Integrable.const_mul ?_ _
    refine integrable_of_bdd ((measurable_X_real hX j).mul
      ((measurable_of_countable (fun k => delta f (k + 1))).comp (meas_Y hX.1 n m i _)))
      (1 * (2 * Cf)) ?_
    filter_upwards [hb] with ω hω
    rw [abs_mul]
    have h1 := hXr j ω (hω j)
    have h3 := hdb (Y n m X i ((j : ℤ) - 1) ω + 1)
    gcongr
  have iS1 : Integrable (fun ω => ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA i j
  have iS2 : Integrable (fun ω => ∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1)) P :=
    integrable_finsetSum _ fun i _ => iB i
  have iS3 : Integrable (fun ω => ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1))) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iC i j
  rw [integral_congr_ae hpt, integral_sub ?h1 iS3,
    integral_add ?h2 iS2, integral_add (integrable_const _) iS1,
    integral_const, integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ => iA i j),
    integral_finset_sum _ (fun i _ => iB i),
    integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ => iC i j)]
  simp only [probReal_univ, one_smul]
  have eA : ∀ i : ℕ, ∫ ω, (∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
      (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) ∂P
      = ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P :=
    fun i => integral_finset_sum _ fun j _ => iA i j
  have eC : ∀ i : ℕ, ∫ ω, (∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
      prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1))) ∂P
      = ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        prob P X i * ∫ ω, (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by
    intro i
    rw [integral_finset_sum _ fun j _ => iC i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  simp only [eA, eC]
  case h1 => exact ((integrable_const _).add iS1).add iS2
  case h2 => exact (integrable_const _).add iS1

end T41
namespace T41

open PoissonDepTrials.MixSqrt

theorem sigmaIcc_le {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {X : ℕ → Ω → β}
    (hXm : ∀ i, Measurable (X i)) (a b : ℕ) : sigmaIcc X a b ≤ mΩ :=
  iSup₂_le fun i _ => (hXm i).comap_le

theorem sigmaIci_le {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {X : ℕ → Ω → β}
    (hXm : ∀ i, Measurable (X i)) (a : ℕ) : sigmaIci X a ≤ mΩ :=
  iSup₂_le fun i _ => (hXm i).comap_le

theorem meas_sigmaIcc {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b i : ℕ)
    (hi : i ∈ Finset.Icc a b) : Measurable[sigmaIcc X a b] (X i) :=
  Measurable.mono (comap_measurable (X i))
    (le_iSup₂ (f := fun i (_ : i ∈ Finset.Icc a b) => MeasurableSpace.comap (X i) inferInstance)
      i hi) le_rfl

theorem meas_sigmaIci {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a i : ℕ)
    (hi : a ≤ i) : Measurable[sigmaIci X a] (X i) :=
  Measurable.mono (comap_measurable (X i))
    (le_iSup₂ (f := fun i (_ : i ∈ Set.Ici a) => MeasurableSpace.comap (X i) inferInstance)
      i (Set.mem_Ici.mpr hi)) le_rfl

/-- Key covariance bound from (4.1). -/
theorem mix_cov {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → β) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (U : Ω → ℝ)
    (hU : StronglyMeasurable[sigmaIcc X 1 j] U) (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ)
    (hUC : ∀ ω, U ω ≤ C) (B : Set Ω) (hB : MeasurableSet[sigmaIci X (j + k)] B) :
    |∫ ω, U ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P - (∫ ω, U ω ∂P) * P.real B|
      ≤ φ k * ∫ ω, U ω ∂P := by
  have hle := sigmaIcc_le hXm 1 j
  have hBm : MeasurableSet B := sigmaIci_le hXm (j + k) B hB
  have hb := hφ.2.2 j k hj hk B hB
  set g : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hg
  have hg1 : ∀ ω, |g ω| ≤ 1 := fun ω => by
    rw [hg]; unfold Set.indicator; split_ifs <;> simp
  have hgi : Integrable g P := (integrable_const (1 : ℝ)).indicator hBm
  have hUm : StronglyMeasurable U := hU.mono hle
  have hUi : Integrable U P := Integrable.of_bound hUm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 ω)]; exact hUC ω)
  have hUgi : Integrable (U * g) P := by
    refine Integrable.of_bound (hUm.mul (stronglyMeasurable_const.indicator hBm)).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (hU0 ω)]
    nlinarith [hU0 ω, hUC ω, hg1 ω, abs_nonneg (g ω)]
  have hce := condExp_mul_of_stronglyMeasurable_left hU hUgi hgi
  have hci : Integrable (fun ω => U ω * (P[g | sigmaIcc X 1 j]) ω) P :=
    integrable_condExp.congr hce
  have h1 : ∫ ω, U ω * g ω ∂P = ∫ ω, U ω * (P[g | sigmaIcc X 1 j]) ω ∂P := by
    rw [← integral_condExp hle (f := fun ω => U ω * g ω)]
    exact integral_congr_ae hce
  have h2 : ∫ ω, U ω * (P[g | sigmaIcc X 1 j]) ω ∂P - (∫ ω, U ω ∂P) * P.real B
      = ∫ ω, U ω * ((P[g | sigmaIcc X 1 j]) ω - P.real B) ∂P := by
    rw [← integral_mul_const, ← integral_sub hci (hUi.mul_const _)]
    congr 1
    ext ω
    ring
  rw [h1, h2, ← integral_const_mul]
  have := norm_integral_le_of_norm_le (hUi.const_mul (φ k))
    (f := fun ω => U ω * ((P[g | sigmaIcc X 1 j]) ω - P.real B)) (hb.mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU0 ω), mul_comm (φ k)]
      exact mul_le_mul_of_nonneg_left hω (hU0 ω))
  rwa [Real.norm_eq_abs] at this

theorem far_cov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m a b : ℕ) (ha : 1 ≤ a) (hab : a + m + 1 ≤ b) :
    |∫ ω, (X a ω : ℝ) * X b ω ∂P - prob P X a * prob P X b| ≤ φ (m + 1) * prob P X a := by
  set U : Ω → ℝ := fun ω => if X a ω = 1 then 1 else 0 with hUdef
  set B : Set Ω := {ω | X b ω = 1} with hBdef
  have hUa : (fun ω => (X a ω : ℝ)) =ᵐ[P] U := by
    filter_upwards [hX.2.2 a] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h | h <;> simp [hUdef, h]
  have hXb : (fun ω => (X b ω : ℝ)) =ᵐ[P] B.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hX.2.2 b] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h | h <;>
      simp [hBdef, Set.indicator_apply, h]
  have hU : StronglyMeasurable[sigmaIcc X 1 a] U :=
    ((measurable_of_countable (fun x : ℕ => if x = 1 then (1 : ℝ) else 0)).comp
      (meas_sigmaIcc X 1 a a (Finset.mem_Icc.mpr ⟨ha, le_rfl⟩))).stronglyMeasurable
  have hB : MeasurableSet[sigmaIci X (a + (b - a))] B :=
    meas_sigmaIci X (a + (b - a)) b (by omega) (measurableSet_singleton 1)
  have key := mix_cov P X hX.1 φ hφ a (b - a) ha (by omega) U hU
    (fun ω => by simp only [hUdef]; split_ifs <;> norm_num) 1
    (fun ω => by simp only [hUdef]; split_ifs <;> norm_num) B hB
  have hEU : ∫ ω, U ω ∂P = prob P X a := by
    rw [← integral_congr_ae hUa]; exact integral_X_eq_prob P n X hX a
  have hPB : P.real B = prob P X b := rfl
  have hEUB : ∫ ω, U ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P = ∫ ω, (X a ω : ℝ) * X b ω ∂P :=
    integral_congr_ae (hUa.symm.mul hXb.symm)
  rw [hEUB, hEU, hPB] at key
  have hφm : φ (b - a) ≤ φ (m + 1) := hφ.1 (by omega)
  calc _ ≤ φ (b - a) * prob P X a := key
    _ ≤ φ (m + 1) * prob P X a := mul_le_mul_of_nonneg_right hφm (prob_nonneg P X a)

theorem far_cov' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : ¬ |(i : ℤ) - (j : ℕ)| ≤ m) :
    |∫ ω, (X i ω : ℝ) * X j ω ∂P - prob P X i * prob P X j|
      ≤ φ (m + 1) * (prob P X i + prob P X j) := by
  have hφ0 : 0 ≤ φ (m + 1) := hφ.1.le_of_tendsto hφ.2.1 (m + 1)
  have pi0 := prob_nonneg P X i
  have pj0 := prob_nonneg P X j
  rw [abs_le] at hij
  push_neg at hij
  by_cases h : (i : ℤ) < j
  · have := far_cov P n X hX φ hφ m i j hi (by omega)
    nlinarith
  · have := far_cov P n X hX φ hφ m j i hj (by omega)
    have e : ∫ ω, (X j ω : ℝ) * X i ω ∂P - prob P X j * prob P X i
        = ∫ ω, (X i ω : ℝ) * X j ω ∂P - prob P X i * prob P X j := by
      simp only [mul_comm]
    rw [e] at this
    nlinarith

theorem integral_XX_self {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (i : ℕ) :
    ∫ ω, (X i ω : ℝ) * X i ω ∂P = prob P X i := by
  rw [← integral_X_eq_prob P n X hX i]
  refine integral_congr_ae ?_
  filter_upwards [hX.2.2 i] with ω hω
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h | h <;> simp [h]

theorem split_near (n m i : ℕ) (hi : i ∈ Finset.Icc 1 n) (F : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 n, F j = F i
      + ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m, F j
      + ∑ j ∈ Finset.Icc 1 n with ¬ |(i : ℤ) - (j : ℕ)| ≤ m, F j := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)) (fun j => j = i)]
  have e1 : ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)).filter
      (fun j => j = i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc, abs_le] at hi ⊢
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; refine ⟨⟨hi, by omega, by omega⟩, rfl⟩
  have e2 : ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - (j : ℕ)| ≤ m)).filter
      (fun j => ¬ j = i) = (Finset.Icc 1 n).filter
        (fun j : ℕ => 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun j _ => by simp only [abs_le, abs_pos, ne_eq]; omega
  rw [e1, e2, Finset.sum_singleton]

theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P
      ≤ Var[fun ω => (W n X ω : ℝ); P] - lam P n X + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
        + 4 * lam P n X * n * φ (m + 1) := by
  have hb : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX.2.2
  have hφ0 : 0 ≤ φ (m + 1) := hφ.1.le_of_tendsto hφ.2.1 (m + 1)
  have hL0 : 0 ≤ lam P n X := Finset.sum_nonneg fun i _ => prob_nonneg P X i
  have hWr : (fun ω => (W n X ω : ℝ)) = fun ω => ∑ i ∈ Finset.Icc 1 n, (X i ω : ℝ) := by
    funext ω; simp [W]
  have hWm : Measurable (fun ω => (W n X ω : ℝ)) := by
    rw [hWr]; exact Finset.measurable_sum _ fun i _ => measurable_X_real hX i
  have hWb : ∀ᵐ ω ∂P, ‖(W n X ω : ℝ)‖ ≤ n := by
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have : W n X ω ≤ n := by
      simp only [W]
      calc ∑ i ∈ Finset.Icc 1 n, X i ω ≤ ∑ i ∈ Finset.Icc 1 n, 1 := Finset.sum_le_sum fun i _ => hω i
        _ = n := by simp
    exact_mod_cast this
  have hmem : MemLp (fun ω => (W n X ω : ℝ)) 2 P :=
    MemLp.of_bound hWm.aestronglyMeasurable n hWb
  rw [variance_eq_sub hmem]
  have hEW : ∫ ω, (W n X ω : ℝ) ∂P = lam P n X := by
    rw [hWr, integral_finset_sum _ (fun i _ => integrable_X hX i)]
    exact Finset.sum_congr rfl fun i _ => integral_X_eq_prob P n X hX i
  have hEW2 : ∫ ω, ((fun ω => (W n X ω : ℝ)) ^ 2) ω ∂P
      = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∫ ω, (X i ω : ℝ) * X j ω ∂P := by
    have e : (fun ω => (W n X ω : ℝ)) ^ 2
        = fun ω => ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, (X i ω : ℝ) * X j ω := by
      funext ω
      rw [Pi.pow_apply, show ((W n X ω : ℕ) : ℝ) = ∑ i ∈ Finset.Icc 1 n, (X i ω : ℝ) from congrFun hWr ω,
        sq, Finset.sum_mul_sum]
    rw [e, integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ => integrable_XX hX i j)]
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => integrable_XX hX i j
  rw [hEW, hEW2]
  -- decompose
  set p := prob P X with hp
  set Nn := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P with hNn
  set Fa := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with ¬ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P with hFa
  set Pn := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i * p j with hPn
  set Pf := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with ¬ |(i : ℤ) - (j : ℕ)| ≤ m, p i * p j
    with hPf
  have hL : lam P n X = ∑ i ∈ Finset.Icc 1 n, p i := rfl
  have hS : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∫ ω, (X i ω : ℝ) * X j ω ∂P
      = lam P n X + Nn + Fa := by
    rw [hL, hNn, hFa, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [split_near n m i hi, integral_XX_self P n X hX i]
  have hL2 : lam P n X ^ 2 = Pn + Pf := by
    rw [hL, sq, Finset.sum_mul_sum, hPn, hPf, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcs : Pn ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 := cs410_real n m p
  have hfar : -(2 * n * lam P n X * φ (m + 1)) ≤ Fa - Pf := by
    have h1 : |Fa - Pf| ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n,
        φ (m + 1) * (p i + p j) := by
      rw [hFa, hPf, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ Finset.Icc 1 n with ¬ |(i : ℤ) - (j : ℕ)| ≤ m,
            |∫ ω, (X i ω : ℝ) * X j ω ∂P - p i * p j|
          ≤ ∑ j ∈ Finset.Icc 1 n with ¬ |(i : ℤ) - (j : ℕ)| ≤ m, φ (m + 1) * (p i + p j) :=
            Finset.sum_le_sum fun j hj => by
              have hj' := Finset.mem_filter.mp hj
              exact far_cov' P n X hX φ hφ m i j (Finset.mem_Icc.mp hi).1
                (Finset.mem_Icc.mp hj'.1).1 hj'.2
        _ ≤ ∑ j ∈ Finset.Icc 1 n, φ (m + 1) * (p i + p j) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ =>
              mul_nonneg hφ0 (add_nonneg (prob_nonneg P X i) (prob_nonneg P X j)))
    have h2 : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, φ (m + 1) * (p i + p j)
        = 2 * n * lam P n X * φ (m + 1) := by
      have e : ∀ i, ∑ j ∈ Finset.Icc 1 n, φ (m + 1) * (p i + p j)
          = φ (m + 1) * (n * p i + lam P n X) := by
        intro i
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← hL]
        simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, ← hL]
      simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    have := neg_abs_le (Fa - Pf)
    linarith
  have hnL : 0 ≤ (n : ℝ) * lam P n X * φ (m + 1) := by positivity
  rw [hS, hL2]
  nlinarith
end T41
namespace T41

open PoissonDepTrials.MixSqrt

theorem ind_abs_le_one {Ω : Type*} (S : Set Ω) (ω : Ω) :
    |S.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
  unfold Set.indicator; split_ifs <;> simp

theorem ind_nonneg {Ω : Type*} (S : Set Ω) (ω : Ω) : 0 ≤ S.indicator (fun _ => (1 : ℝ)) ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) ω

theorem ind_le_one {Ω : Type*} (S : Set Ω) (ω : Ω) : S.indicator (fun _ => (1 : ℝ)) ω ≤ 1 :=
  (le_abs_self _).trans (ind_abs_le_one S ω)

theorem sum_ind_eq {Ω : Type*} (Z : Ω → ℕ) (S : Finset ℕ) (ω : Ω) :
    ∑ b ∈ S, {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) ω
      = (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω := by
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_ite_eq]
  unfold Set.indicator
  split_ifs <;> simp_all

theorem sum_ind_le_one {Ω : Type*} (Z : Ω → ℕ) (S : Finset ℕ) (ω : Ω) :
    ∑ b ∈ S, {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
  rw [sum_ind_eq]; exact ind_le_one _ ω

theorem int_mul_ind {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : Ω → ℝ} (hUm : StronglyMeasurable U) (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ) (hUC : ∀ ω, U ω ≤ C)
    (S : Set Ω) (hS : MeasurableSet S) :
    Integrable (fun ω => U ω * S.indicator (fun _ => (1 : ℝ)) ω) P := by
  refine Integrable.of_bound (hUm.mul (stronglyMeasurable_const.indicator hS)).aestronglyMeasurable
    C (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU0 ω)]
  nlinarith [hU0 ω, hUC ω, ind_abs_le_one S ω, abs_nonneg (S.indicator (fun _ => (1 : ℝ)) ω)]

/-- Covariance bound for a bounded function of a future `ℕ`-valued variable. -/
theorem mix_cov_fun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (U : Ω → ℝ) (hU : StronglyMeasurable[sigmaIcc X 1 j] U)
    (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ) (hUC : ∀ ω, U ω ≤ C)
    (Z : Ω → ℕ) (hZ : Measurable[sigmaIci X (j + k)] Z) (N : ℕ) (hZN : ∀ᵐ ω ∂P, Z ω ≤ N)
    (g : ℕ → ℝ) (M : ℝ) (hg : ∀ b, |g b| ≤ M) :
    |∫ ω, U ω * g (Z ω) ∂P - (∫ ω, U ω ∂P) * ∫ ω, g (Z ω) ∂P|
      ≤ 2 * M * (φ k * ∫ ω, U ω ∂P) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hg 0)
  have hZm : Measurable Z := hZ.mono (sigmaIci_le hXm _) le_rfl
  have hUm : StronglyMeasurable U := hU.mono (sigmaIcc_le hXm 1 j)
  have hUi : Integrable U P := Integrable.of_bound hUm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 ω)]; exact hUC ω)
  set R := Finset.range (N + 1) with hR
  set I : ℕ → Ω → ℝ := fun b => {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) with hI
  have hIm : ∀ b, MeasurableSet {ω | Z ω = b} := fun b => hZm (measurableSet_singleton b)
  have hIi : ∀ b, Integrable (I b) P := fun b => (integrable_const (1 : ℝ)).indicator (hIm b)
  have hUIi : ∀ b, Integrable (fun ω => U ω * I b ω) P := fun b =>
    int_mul_ind hUm hU0 C hUC _ (hIm b)
  have hdec : ∀ᵐ ω ∂P, g (Z ω) = ∑ b ∈ R, g b * I b ω := by
    filter_upwards [hZN] with ω hω
    simp only [hI, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))]
  have hdecU : ∀ᵐ ω ∂P, U ω * g (Z ω) = ∑ b ∈ R, g b * (U ω * I b ω) := by
    filter_upwards [hdec] with ω hω
    rw [hω, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e1 : ∫ ω, U ω * g (Z ω) ∂P = ∑ b ∈ R, g b * ∫ ω, U ω * I b ω ∂P := by
    rw [integral_congr_ae hdecU, integral_finset_sum _ fun b _ => (hUIi b).const_mul (g b)]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  have e2 : ∫ ω, g (Z ω) ∂P = ∑ b ∈ R, g b * ∫ ω, I b ω ∂P := by
    rw [integral_congr_ae hdec, integral_finset_sum _ fun b _ => (hIi b).const_mul (g b)]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  set c : ℕ → ℝ := fun b => ∫ ω, U ω * I b ω ∂P - (∫ ω, U ω ∂P) * ∫ ω, I b ω ∂P with hc
  have e3 : ∫ ω, U ω * g (Z ω) ∂P - (∫ ω, U ω ∂P) * ∫ ω, g (Z ω) ∂P = ∑ b ∈ R, g b * c b := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by simp only [hc]; ring
  have hS : ∀ S : Finset ℕ, |∑ b ∈ S, c b| ≤ φ k * ∫ ω, U ω ∂P := by
    intro S
    have hB : MeasurableSet[sigmaIci X (j + k)] (Z ⁻¹' (S : Set ℕ)) :=
      hZ (Set.Finite.measurableSet S.finite_toSet)
    have hBm : MeasurableSet (Z ⁻¹' (S : Set ℕ)) := hZm (Set.Finite.measurableSet S.finite_toSet)
    have key := mix_cov P X hXm φ hφ j k hj hk U hU hU0 C hUC _ hB
    have s1 : ∑ b ∈ S, ∫ ω, U ω * I b ω ∂P
        = ∫ ω, U ω * (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [← integral_finset_sum _ fun b _ => hUIi b]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [← Finset.mul_sum, sum_ind_eq]
    have s2 : ∑ b ∈ S, ∫ ω, I b ω ∂P = P.real (Z ⁻¹' (S : Set ℕ)) := by
      rw [← integral_finset_sum _ fun b _ => hIi b, ← integral_indicator_one hBm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hI]
      rw [sum_ind_eq]
      rfl
    have : ∑ b ∈ S, c b = ∫ ω, U ω * (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω ∂P
        - (∫ ω, U ω ∂P) * P.real (Z ⁻¹' (S : Set ℕ)) := by
      simp only [hc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2]
    rw [this]; exact key
  have habs : ∑ b ∈ R, |c b| ≤ 2 * (φ k * ∫ ω, U ω ∂P) := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun b => 0 ≤ c b)]
    have h1 : ∑ b ∈ R with 0 ≤ c b, |c b| = ∑ b ∈ R with 0 ≤ c b, c b :=
      Finset.sum_congr rfl fun b hb => abs_of_nonneg (Finset.mem_filter.mp hb).2
    have h2 : ∑ b ∈ R with ¬ 0 ≤ c b, |c b| = -∑ b ∈ R with ¬ 0 ≤ c b, c b := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b hb => abs_of_neg (not_le.mp (Finset.mem_filter.mp hb).2)
    rw [h1, h2]
    have a1 := hS (R.filter (fun b => 0 ≤ c b))
    have a2 := hS (R.filter (fun b => ¬ 0 ≤ c b))
    have := le_abs_self (∑ b ∈ R with 0 ≤ c b, c b)
    have := neg_abs_le (∑ b ∈ R with ¬ 0 ≤ c b, c b)
    linarith
  rw [e3]
  calc |∑ b ∈ R, g b * c b| ≤ ∑ b ∈ R, |g b * c b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ R, M * |c b| := Finset.sum_le_sum fun b _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hg b) (abs_nonneg _)
    _ = M * ∑ b ∈ R, |c b| := by rw [Finset.mul_sum]
    _ ≤ M * (2 * (φ k * ∫ ω, U ω ∂P)) := mul_le_mul_of_nonneg_left habs hM0
    _ = 2 * M * (φ k * ∫ ω, U ω ∂P) := by ring

theorem V_split {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    V n m X i ω = ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k + m < i), X k ω
      + ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => i + m < k), X k ω := by
  simp only [V]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i))) (fun k => k + m < i)]
  congr 1
  · rw [Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun _ _ => rfl
  · rw [Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun _ _ => rfl

theorem sum_filter_le_n {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (q : ℕ → Prop) [DecidablePred q]
    (ω : Ω) (hω : ∀ k, X k ω ≤ 1) :
    ∑ k ∈ (Finset.Icc 1 n).filter q, X k ω ≤ n := by
  calc ∑ k ∈ (Finset.Icc 1 n).filter q, X k ω ≤ ∑ k ∈ (Finset.Icc 1 n).filter q, 1 :=
        Finset.sum_le_sum fun k _ => hω k
    _ = ((Finset.Icc 1 n).filter q).card := by simp
    _ ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem per_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
    |∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P| ≤ 6 * M * φ (m + 1) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => hφ.1.le_of_tendsto hφ.2.1 k
  have hb : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX.2.2
  have hp0 := prob_nonneg P X i
  have hp1 : prob P X i ≤ 1 := measureReal_le_one
  set A : Ω → ℕ := fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k + m < i), X k ω with hA
  set B : Ω → ℕ := fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => i + m < k), X k ω with hB
  set U : Ω → ℝ := {ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) with hU
  have hV : ∀ ω, V n m X i ω = A ω + B ω := fun ω => V_split n m X i ω
  have hUa : (fun ω => (X i ω : ℝ)) =ᵐ[P] U := by
    filter_upwards [hX.2.2 i] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h | h <;> simp [hU, h]
  have hEU : ∫ ω, U ω ∂P = prob P X i := by
    rw [← integral_congr_ae hUa]; exact integral_X_eq_prob P n X hX i
  have hUms : MeasurableSet {ω | X i ω = 1} := (hX.1 i) (measurableSet_singleton 1)
  have hUsm : StronglyMeasurable[sigmaIcc X 1 i] U :=
    (stronglyMeasurable_const.indicator
      ((meas_sigmaIcc X 1 i i (Finset.mem_Icc.mpr ⟨hi1, le_rfl⟩)) (measurableSet_singleton 1)))
  have hBm : Measurable[sigmaIci X (i + (m + 1))] B :=
    Finset.measurable_sum _ fun k hk => meas_sigmaIci X _ k (by
      have := (Finset.mem_filter.mp hk).2; omega)
  have hBN : ∀ᵐ ω ∂P, B ω ≤ n := hb.mono fun ω hω => sum_filter_le_n n X _ ω hω
  have hAN : ∀ᵐ ω ∂P, A ω ≤ n := hb.mono fun ω hω => sum_filter_le_n n X _ ω hω
  have hAm' : ∀ J, i ≤ J + m + 1 → Measurable[sigmaIcc X 1 J] A := fun J hJ =>
    Finset.measurable_sum _ fun k hk => meas_sigmaIcc X 1 J k (by
      have h1 := Finset.mem_filter.mp hk
      have h2 := Finset.mem_Icc.mp h1.1
      exact Finset.mem_Icc.mpr ⟨h2.1, by omega⟩)
  have hAm : Measurable A := (hAm' i (by omega)).mono (sigmaIcc_le hX.1 1 i) le_rfl
  have hBmm : Measurable B := hBm.mono (sigmaIci_le hX.1 _) le_rfl
  have hfV : Measurable (fun ω => f (A ω + B ω + 1)) :=
    (measurable_of_countable (fun k : ℕ => f (k + 1))).comp (hAm.add hBmm)
  have hfVi : Integrable (fun ω => f (A ω + B ω + 1)) P :=
    Integrable.of_bound hfV.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM _)
  have hUf : Integrable (fun ω => U ω * f (A ω + B ω + 1)) P := by
    refine Integrable.of_bound ((stronglyMeasurable_const.indicator hUms).mul
      hfV.stronglyMeasurable).aestronglyMeasurable M (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [ind_abs_le_one {ω | X i ω = 1} ω, abs_nonneg (f (A ω + B ω + 1)), hM (A ω + B ω + 1),
      abs_nonneg ({ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) ω)]
  -- rewrite the integral
  have hmain : ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P
      = ∫ ω, U ω * f (A ω + B ω + 1) ∂P - (∫ ω, U ω ∂P) * ∫ ω, f (A ω + B ω + 1) ∂P := by
    rw [hEU, ← integral_const_mul, ← integral_sub hUf (hfVi.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [hUa] with ω hω
    rw [hV ω, ← hω]
    ring
  rw [hmain]
  have hU01 : ∀ ω, 0 ≤ U ω ∧ U ω ≤ 1 := fun ω => ⟨ind_nonneg _ ω, ind_le_one _ ω⟩
  have hUsm' : StronglyMeasurable U := stronglyMeasurable_const.indicator hUms
  have hUi : Integrable U P := (integrable_const (1 : ℝ)).indicator hUms
  have hMφ : 0 ≤ M * φ (m + 1) := mul_nonneg hM0 (hφ0 _)
  rcases le_or_gt i (m + 1) with hsmall | hbig
  · have hA0 : ∀ ω, A ω = 0 := fun ω => by
      simp only [hA]
      apply Finset.sum_eq_zero
      intro k hk
      have h1 := Finset.mem_filter.mp hk
      have h2 := Finset.mem_Icc.mp h1.1
      exfalso; omega
    simp only [hA0, zero_add]
    have h := mix_cov_fun P X hX.1 φ hφ i (m + 1) hi1 (by omega) U hUsm (fun ω => (hU01 ω).1) 1
      (fun ω => (hU01 ω).2) B hBm n hBN (fun b => f (b + 1)) M (fun b => hM _)
    calc _ ≤ 2 * M * (φ (m + 1) * ∫ ω, U ω ∂P) := h
      _ = 2 * M * (φ (m + 1) * prob P X i) := by rw [hEU]
      _ ≤ 6 * M * φ (m + 1) := by nlinarith [mul_le_mul_of_nonneg_left hp1 hMφ]
  · obtain ⟨J, hJ⟩ : ∃ J, i = J + m + 1 := ⟨i - m - 1, by omega⟩
    have hJ1 : 1 ≤ J := by omega
    set R := Finset.range (n + 1) with hR
    set I : ℕ → Ω → ℝ := fun a => {ω | A ω = a}.indicator (fun _ => (1 : ℝ)) with hI
    have hI01 : ∀ a ω, 0 ≤ I a ω ∧ I a ω ≤ 1 := fun a ω => ⟨ind_nonneg _ ω, ind_le_one _ ω⟩
    have hIm : ∀ a, MeasurableSet {ω | A ω = a} := fun a => hAm (measurableSet_singleton a)
    have hIsm : ∀ a, StronglyMeasurable[sigmaIcc X 1 J] (I a) := fun a =>
      stronglyMeasurable_const.indicator ((hAm' J (by omega)) (measurableSet_singleton a))
    have hIsmi : ∀ a, StronglyMeasurable[sigmaIcc X 1 i] (I a) := fun a =>
      stronglyMeasurable_const.indicator ((hAm' i (by omega)) (measurableSet_singleton a))
    have hIsm' : ∀ a, StronglyMeasurable (I a) := fun a =>
      stronglyMeasurable_const.indicator (hIm a)
    have hIi : ∀ a, Integrable (I a) P := fun a => (integrable_const (1 : ℝ)).indicator (hIm a)
    have hgB : ∀ a : ℕ, Measurable (fun ω => f (a + B ω + 1)) := fun a =>
      (measurable_of_countable (fun b : ℕ => f (a + b + 1))).comp hBmm
    have hIg : ∀ a, Integrable (fun ω => I a ω * f (a + B ω + 1)) P := fun a => by
      refine Integrable.of_bound ((hIsm' a).mul (hgB a).stronglyMeasurable).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hI01 a ω).1]
      nlinarith [hI01 a ω, hM (a + B ω + 1), abs_nonneg (f (a + B ω + 1))]
    have hUIg : ∀ a, Integrable (fun ω => U ω * I a ω * f (a + B ω + 1)) P := fun a => by
      refine Integrable.of_bound ((hUsm'.mul (hIsm' a)).mul
        (hgB a).stronglyMeasurable).aestronglyMeasurable M (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hU01 ω).1 (hI01 a ω).1)]
      have h01 : U ω * I a ω ≤ 1 := by nlinarith [hU01 ω, hI01 a ω]
      nlinarith [mul_nonneg (hU01 ω).1 (hI01 a ω).1, hM (a + B ω + 1), abs_nonneg (f (a + B ω + 1))]
    have hUIi : ∀ a, Integrable (fun ω => U ω * I a ω) P := fun a =>
      int_mul_ind hUsm' (fun ω => (hU01 ω).1) 1 (fun ω => (hU01 ω).2) _ (hIm a)
    have hdec : ∀ᵐ ω ∂P, f (A ω + B ω + 1) = ∑ a ∈ R, I a ω * f (a + B ω + 1) := by
      filter_upwards [hAN] with ω hω
      simp only [hI, Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))]
    have hT1 : ∫ ω, U ω * f (A ω + B ω + 1) ∂P
        = ∑ a ∈ R, ∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P := by
      rw [← integral_finset_sum _ fun a _ => hUIg a]
      refine integral_congr_ae ?_
      filter_upwards [hdec] with ω hω
      rw [hω, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hT2 : ∫ ω, f (A ω + B ω + 1) ∂P = ∑ a ∈ R, ∫ ω, I a ω * f (a + B ω + 1) ∂P := by
      rw [← integral_finset_sum _ fun a _ => hIg a]
      exact integral_congr_ae hdec
    set α : ℕ → ℝ := fun a => ∫ ω, U ω * I a ω ∂P with hα
    set β : ℕ → ℝ := fun a => ∫ ω, I a ω ∂P with hβ
    set G : ℕ → ℝ := fun a => ∫ ω, f (a + B ω + 1) ∂P with hG
    have hG1 : ∀ a, |G a| ≤ M := fun a => by
      have := norm_integral_le_of_norm_le (integrable_const M) (μ := P)
        (f := fun ω => f (a + B ω + 1))
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM (a + B ω + 1))
      simpa [Real.norm_eq_abs] using this
    have hα0 : ∀ a, 0 ≤ α a := fun a =>
      integral_nonneg fun ω => mul_nonneg (hU01 ω).1 (hI01 a ω).1
    have hβ0 : ∀ a, 0 ≤ β a := fun a => integral_nonneg fun ω => (hI01 a ω).1
    have e1 : ∀ a, |∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P - α a * G a|
        ≤ 2 * M * (φ (m + 1) * α a) := fun a =>
      mix_cov_fun P X hX.1 φ hφ i (m + 1) hi1 (by omega) (fun ω => U ω * I a ω)
        (hUsm.mul (hIsmi a)) (fun ω => mul_nonneg (hU01 ω).1 (hI01 a ω).1) 1
        (fun ω => by nlinarith [hU01 ω, hI01 a ω])
        B hBm n hBN (fun b => f (a + b + 1)) M (fun b => hM _)
    have hBm2 : Measurable[sigmaIci X (J + (2 * m + 2))] B := by
      rw [show J + (2 * m + 2) = i + (m + 1) by omega]; exact hBm
    have e3 : ∀ a, |∫ ω, I a ω * f (a + B ω + 1) ∂P - β a * G a|
        ≤ 2 * M * (φ (m + 1) * β a) := fun a => by
      have h := mix_cov_fun P X hX.1 φ hφ J (2 * m + 2) hJ1 (by omega) (I a) (hIsm a)
        (fun ω => (hI01 a ω).1) 1 (fun ω => (hI01 a ω).2) B hBm2 n hBN
        (fun b => f (a + b + 1)) M (fun b => hM _)
      have hφa : φ (2 * m + 2) ≤ φ (m + 1) := hφ.1 (by omega)
      calc _ ≤ 2 * M * (φ (2 * m + 2) * β a) := h
        _ ≤ 2 * M * (φ (m + 1) * β a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφa (hβ0 a)) (by linarith)
    have hXi_meas : MeasurableSet[sigmaIci X (J + (m + 1))] {ω | X i ω = 1} :=
      meas_sigmaIci X (J + (m + 1)) i (by omega) (measurableSet_singleton 1)
    have e2 : ∀ a, |α a - prob P X i * β a| ≤ φ (m + 1) * β a := fun a => by
      have h := mix_cov P X hX.1 φ hφ J (m + 1) hJ1 (by omega) (I a) (hIsm a)
        (fun ω => (hI01 a ω).1) 1 (fun ω => (hI01 a ω).2) _ hXi_meas
      have h1 : ∫ ω, I a ω * {ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) ω ∂P = α a :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      have h2 : P.real {ω | X i ω = 1} = prob P X i := rfl
      rw [h1, h2] at h
      calc |α a - prob P X i * β a| = |α a - β a * prob P X i| := by rw [mul_comm (prob P X i)]
        _ ≤ φ (m + 1) * β a := h
    have hsα : ∑ a ∈ R, α a ≤ prob P X i := by
      rw [← hEU, ← integral_finset_sum _ fun a _ => hUIi a]
      refine integral_mono (integrable_finsetSum _ fun a _ => hUIi a) hUi fun ω => ?_
      show ∑ a ∈ R, U ω * I a ω ≤ U ω
      rw [← Finset.mul_sum]
      have := sum_ind_le_one A R ω
      nlinarith [hU01 ω]
    have hsβ : ∑ a ∈ R, β a ≤ 1 := by
      rw [← integral_finset_sum _ fun a _ => hIi a]
      have := integral_mono (integrable_finsetSum _ fun a _ => hIi a) (integrable_const (1 : ℝ))
        (μ := P) fun ω => sum_ind_le_one A R ω
      simpa using this
    rw [hT1, hT2, hEU, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have per : ∀ a ∈ R, |∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P
        - prob P X i * ∫ ω, I a ω * f (a + B ω + 1) ∂P|
        ≤ M * φ (m + 1) * β a + 2 * M * φ (m + 1) * α a
          + 2 * M * φ (m + 1) * prob P X i * β a := by
      intro a _
      have h1 := e1 a
      have h2 := e2 a
      have h3 := e3 a
      have hg := hG1 a
      set P1 := ∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P
      set Q1 := ∫ ω, I a ω * f (a + B ω + 1) ∂P
      have eq : P1 - prob P X i * Q1 = (α a - prob P X i * β a) * G a + (P1 - α a * G a)
          - prob P X i * (Q1 - β a * G a) := by ring
      rw [eq]
      have k1 : |(α a - prob P X i * β a) * G a| ≤ φ (m + 1) * β a * M := by
        rw [abs_mul]
        exact mul_le_mul h2 hg (abs_nonneg _) (mul_nonneg (hφ0 _) (hβ0 a))
      have k3 : |prob P X i * (Q1 - β a * G a)| ≤ prob P X i * (2 * M * (φ (m + 1) * β a)) := by
        rw [abs_mul, abs_of_nonneg hp0]
        exact mul_le_mul_of_nonneg_left h3 hp0
      have t1 := abs_sub ((α a - prob P X i * β a) * G a + (P1 - α a * G a))
        (prob P X i * (Q1 - β a * G a))
      have t2 := abs_add_le ((α a - prob P X i * β a) * G a) (P1 - α a * G a)
      nlinarith
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ R, (M * φ (m + 1) * β a + 2 * M * φ (m + 1) * α a
          + 2 * M * φ (m + 1) * prob P X i * β a) := Finset.sum_le_sum per
      _ = M * φ (m + 1) * ∑ a ∈ R, β a + 2 * M * φ (m + 1) * ∑ a ∈ R, α a
          + 2 * M * φ (m + 1) * prob P X i * ∑ a ∈ R, β a := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ ≤ 6 * M * φ (m + 1) := by
          have hsβ0 : 0 ≤ ∑ a ∈ R, β a := Finset.sum_nonneg fun a _ => hβ0 a
          nlinarith [mul_le_mul_of_nonneg_left hsβ hMφ, mul_le_mul_of_nonneg_left hsα hMφ,
            mul_le_mul_of_nonneg_left (mul_le_mul hp1 hsβ hsβ0 zero_le_one) hMφ,
            mul_le_mul_of_nonneg_left hp1 hMφ]

theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by
  calc _ ≤ ∑ i ∈ Finset.Icc 1 n, |∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 n, 6 * M * φ (m + 1) :=
        Finset.sum_le_sum fun i hi => per_i P n X hX φ hφ m f M hM i hi
    _ = 6 * M * n * φ (m + 1) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

end T41
namespace T41

open PoissonDepTrials.MixSqrt

theorem main_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1)
    (hpos : 0 < lam P n X) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h|
      ≤ 6 * min (1 / Real.sqrt (lam P n X)) 1 * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (lam P n X + 1) * n * φ (m + 1)) := by
  set L := lam P n X with hL
  set μ := min (1 / Real.sqrt L) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (by positivity) zero_le_one
  have h34 := A03F915D.lemma_3_4 L hpos h 1 hh
  have h33 := lemma_3_3 L hpos h 1 hh
  have hid := identity_2_6 P n X hX hpos m h 1 hh
  rw [hid]
  set T1 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta (stein L h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P with hT1
  set T2 := ∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein L h (V n m X i ω + 1) ∂P with hT2
  set T3 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P with hT3
  set S11 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P with hS11
  set Spp := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        prob P X i * prob P X j with hSpp
  -- T1
  have b1 : |T1| ≤ 6 * μ * S11 := by
    calc |T1| ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          |∫ ω, (X i ω : ℝ) * X j ω * delta (stein L h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          6 * μ * ∫ ω, (X i ω : ℝ) * X j ω ∂P := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have := abs_integral_mul_delta_le P (fun ω => (X i ω : ℝ) * X j ω)
            (fun ω => by positivity) (integrable_XX hX i j) (delta (stein L h)) (6 * 1 * μ) h34
            (Y' n m X i ((j : ℤ) - 1))
          simpa using this
      _ = 6 * μ * S11 := by
          rw [hS11, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  -- T3
  have b3 : |T3| ≤ 6 * μ * Spp := by
    calc |T3| ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          |prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          6 * μ * (prob P X i * prob P X j) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have := abs_integral_mul_delta_le P (fun ω => (X j ω : ℝ))
            (fun ω => by positivity) (integrable_X hX j) (delta (stein L h)) (6 * 1 * μ) h34
            (Y n m X i ((j : ℤ) - 1))
          rw [integral_X_eq_prob P n X hX j] at this
          rw [abs_mul, abs_of_nonneg (prob_nonneg P X i)]
          calc prob P X i * |∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P|
              ≤ prob P X i * (6 * 1 * μ * prob P X j) :=
                mul_le_mul_of_nonneg_left this (prob_nonneg P X i)
            _ = 6 * μ * (prob P X i * prob P X j) := by ring
      _ = 6 * μ * Spp := by
          rw [hSpp, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  -- T2
  have hS : ∀ k, |stein L h k| ≤ 4 * μ := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [stein, Finset.range_zero, Finset.sum_empty, mul_zero, neg_zero, abs_zero]
      positivity
    · calc |stein L h k| ≤ 4 * 1 * μ := h33 k hk
        _ = 4 * μ := by ring
  have b2 : |T2| ≤ 6 * (4 * μ) * n * φ (m + 1) :=
    lemma_4_6 P n X hX φ hφ m (stein L h) (4 * μ) hS
  have h45 := lemma_4_5 P n X hX φ hφ m
  have hcs := cs410_real n m (prob P X)
  have c45 := mul_le_mul_of_nonneg_left h45 (by positivity : (0 : ℝ) ≤ 6 * μ)
  have ccs := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 6 * μ)
  have e : poissonExp L h + T1 + T2 - T3 - poissonExp L h = T1 + T2 - T3 := by ring
  rw [e]
  calc |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
        have := abs_add_le (T1 + T2) (-T3)
        have := abs_add_le T1 T2
        rw [sub_eq_add_neg]
        rw [abs_neg] at *
        linarith
    _ ≤ 6 * μ * S11 + 6 * (4 * μ) * n * φ (m + 1) + 6 * μ * Spp := by linarith
    _ ≤ 6 * μ * (Var[fun ω => (W n X ω : ℝ); P] - L + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
          + 4 * L * n * φ (m + 1)) + 6 * (4 * μ) * n * φ (m + 1)
          + 6 * μ * ((2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) := by linarith
    _ = 6 * μ * (Var[fun ω => (W n X ω : ℝ); P] - L
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (L + 1) * n * φ (m + 1)) := by
        ring

theorem main_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (h : ℕ → ℝ)
    (hl : lam P n X = 0) :
    ∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h = 0 := by
  have hs : ∑ i ∈ Finset.Icc 1 n, prob P X i = 0 := hl
  have hXi : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X i ω = 0 := by
    intro i hi
    have hp : prob P X i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => prob_nonneg P X i)).mp hs i hi
    have hz : P {ω | X i ω = 1} = 0 := (measureReal_eq_zero_iff (μ := P) (s := {ω | X i ω = 1})).mp hp
    have hne : ∀ᵐ ω ∂P, X i ω ≠ 1 := by
      rw [ae_iff]
      simpa using hz
    filter_upwards [hne, hX.2.2 i] with ω h1 h2
    omega
  have hW : ∀ᵐ ω ∂P, W n X ω = 0 := by
    have := (Filter.eventually_all_finset _).mpr hXi
    filter_upwards [this] with ω hω
    simp only [W]
    exact Finset.sum_eq_zero hω
  have hI : ∫ ω, h (W n X ω) ∂P = h 0 := by
    rw [integral_congr_ae (hW.mono fun ω hω => by simp only [hω] : (fun ω => h (W n X ω)) =ᵐ[P] fun _ => h 0)]
    simp
  have hP : poissonExp 0 h = h 0 := by
    rw [poissonExp, tsum_eq_single 0]
    · simp
    · intro b hb
      simp [zero_pow hb]
  rw [hI, hl, hP, sub_self]

end T41

open MeasureTheory ProbabilityTheory PoissonDepTrials.MixSqrt in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h|
      ≤ 6 * min (1 / Real.sqrt (lam P n X)) 1 * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (lam P n X + 1) * n * φ (m + 1)) := by
  rcases (show 0 ≤ lam P n X from Finset.sum_nonneg fun i _ => T41.prob_nonneg P X i).eq_or_lt
    with h0 | hpos
  · rw [T41.main_zero P n X hX h h0.symm, abs_zero, ← h0]
    simp
  · exact T41.main_pos P n X hX φ hφ m h hh hpos
