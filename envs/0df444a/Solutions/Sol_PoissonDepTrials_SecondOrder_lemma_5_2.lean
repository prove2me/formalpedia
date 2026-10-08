-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:47:45.853846+00:00
-- url     : https://prove2.me/submissions/0c6406a2-1b92-4bbc-a672-cea13947b31a

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace P2M1aceb6c1

lemma pmf_summable (t : ℝ) :
    Summable (fun k : ℕ => Real.exp (-t) * t ^ k / (k.factorial : ℝ)) := by
  have h := (Real.summable_pow_div_factorial t).mul_left (Real.exp (-t))
  refine h.congr (fun k => ?_)
  ring

lemma pmf_nonneg (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ Real.exp (-t) * t ^ k / (k.factorial : ℝ) := by positivity

lemma wsum (t : ℝ) (ht : 0 ≤ t) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ k, |g k| ≤ M) :
    Summable (fun k : ℕ => Real.exp (-t) * t ^ k / (k.factorial : ℝ) * g k) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((pmf_summable t).mul_right M))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pmf_nonneg t ht k)]
  exact mul_le_mul_of_nonneg_left (hg k) (pmf_nonneg t ht k)

lemma low (t b : ℝ) (hb : 0 < b) (hbt : b ≤ t) (k : ℕ) :
    Real.exp (-b) * b ^ k / (k.factorial : ℝ) - Real.exp (-t) * t ^ k / (k.factorial : ℝ) ≤
      (t - b) * (Real.exp (-b) * b ^ k / (k.factorial : ℝ)) := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hpow : b ^ k ≤ t ^ k := pow_le_pow_left₀ hb.le hbt k
  have he : Real.exp (-t) = Real.exp (-b) * Real.exp (-(t - b)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : -(t - b) + 1 ≤ Real.exp (-(t - b)) := Real.add_one_le_exp _
  have heb : 0 < Real.exp (-b) := Real.exp_pos _
  have hbk : 0 ≤ b ^ k := by positivity
  rw [he, div_sub_div_same, mul_div_assoc', div_le_div_iff_of_pos_right hf]
  have h2 : Real.exp (-b) * (-(t - b) + 1) * b ^ k ≤ Real.exp (-b) * Real.exp (-(t - b)) * t ^ k := by
    have := mul_le_mul h1 hpow hbk (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left this heb.le]
  nlinarith [h2]

lemma powdiff (t b : ℝ) (hb : 0 < b) (hbt : b ≤ t) (k : ℕ) :
    t ^ (k + 1) - b ^ (k + 1) ≤ ((k : ℝ) + 1) * (t - b) * t ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hbn : b ^ (n + 1) ≤ t ^ (n + 1) := pow_le_pow_left₀ hb.le hbt _
    have ht : 0 ≤ t := hb.le.trans hbt
    have hd : 0 ≤ t - b := by linarith
    have e1 : t ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        t * (t ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (t - b) := by ring
    rw [e1]
    have h3 : t * (t ^ (n + 1) - b ^ (n + 1)) ≤ t * (((n : ℝ) + 1) * (t - b) * t ^ n) :=
      mul_le_mul_of_nonneg_left ih ht
    have h4 : b ^ (n + 1) * (t - b) ≤ t ^ (n + 1) * (t - b) := mul_le_mul_of_nonneg_right hbn hd
    have e2 : t * (((n : ℝ) + 1) * (t - b) * t ^ n) = ((n : ℝ) + 1) * (t - b) * t ^ (n + 1) := by
      ring
    push_cast
    nlinarith [h3, h4, e2]

lemma up (t b : ℝ) (hb : 0 < b) (hbt : b ≤ t) (k : ℕ) :
    Real.exp (-t) * t ^ (k + 1) / ((k + 1).factorial : ℝ) -
        Real.exp (-b) * b ^ (k + 1) / ((k + 1).factorial : ℝ) ≤
      (t - b) * (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) := by
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hee : Real.exp (-t) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
  have het : 0 < Real.exp (-t) := Real.exp_pos _
  have hbk : 0 ≤ b ^ (k + 1) := by positivity
  have hpd := powdiff t b hb hbt k
  rw [Nat.factorial_succ]
  push_cast
  rw [div_sub_div_same, div_le_iff₀ (by positivity)]
  have h1 : Real.exp (-t) * b ^ (k + 1) ≤ Real.exp (-b) * b ^ (k + 1) :=
    mul_le_mul_of_nonneg_right hee hbk
  have h2 : Real.exp (-t) * (t ^ (k + 1) - b ^ (k + 1)) ≤
      Real.exp (-t) * (((k : ℝ) + 1) * (t - b) * t ^ k) := mul_le_mul_of_nonneg_left hpd het.le
  have e : (t - b) * (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) * (((k : ℝ) + 1) * (k.factorial : ℝ))
      = Real.exp (-t) * (((k : ℝ) + 1) * (t - b) * t ^ k) := by
    field_simp
  rw [e]
  nlinarith [h1, h2]

lemma up0 (t b : ℝ) (hbt : b ≤ t) :
    Real.exp (-t) * t ^ 0 / ((0 : ℕ).factorial : ℝ) -
        Real.exp (-b) * b ^ 0 / ((0 : ℕ).factorial : ℝ) ≤ 0 := by
  have hee : Real.exp (-t) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  linarith

end P2M1aceb6c1

open PoissonDepTrials.SecondOrder in
theorem solution (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (f : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |f k| ≤ M) :
    |poissonExp lam f - poissonExp b f| ≤
      (lam - b) * (poissonExp lam (fun w => |shiftL f w|) + poissonExp b (fun w => |f w|)) := by
  have hl : 0 ≤ lam := hb.le.trans hbl
  have hd : 0 ≤ lam - b := by linarith
  have hMa : ∀ k, |(|f k|)| ≤ M := fun k => by rw [abs_abs]; exact hM k
  have hMs : ∀ k, |(|f (k + 1)|)| ≤ M := fun k => hMa (k + 1)
  set P : ℝ → ℕ → ℝ := fun t k => Real.exp (-t) * t ^ k / (k.factorial : ℝ) with hP
  have sL := P2M1aceb6c1.wsum lam hl f M hM
  have sB := P2M1aceb6c1.wsum b hb.le f M hM
  have sLa := P2M1aceb6c1.wsum lam hl (fun k => |f (k + 1)|) M hMs
  have sBa := P2M1aceb6c1.wsum b hb.le (fun k => |f k|) M hMa
  -- pointwise bound on the pmf difference
  have key0 : |P lam 0 - P b 0| ≤ (lam - b) * P b 0 := by
    rw [abs_le]
    constructor
    · have := P2M1aceb6c1.low lam b hb hbl 0
      simp only [hP] at this ⊢
      linarith
    · have h1 := P2M1aceb6c1.up0 lam b hbl
      have h2 : 0 ≤ (lam - b) * P b 0 := mul_nonneg hd (P2M1aceb6c1.pmf_nonneg b hb.le 0)
      simp only [hP] at h1 h2 ⊢
      linarith
  have keyS : ∀ k : ℕ, |P lam (k + 1) - P b (k + 1)| ≤ (lam - b) * (P lam k + P b (k + 1)) := by
    intro k
    rw [abs_le]
    constructor
    · have := P2M1aceb6c1.low lam b hb hbl (k + 1)
      have h2 : 0 ≤ (lam - b) * P lam k := mul_nonneg hd (P2M1aceb6c1.pmf_nonneg lam hl k)
      simp only [hP] at this h2 ⊢
      nlinarith
    · have h1 := P2M1aceb6c1.up lam b hb hbl k
      have h2 : 0 ≤ (lam - b) * P b (k + 1) := mul_nonneg hd (P2M1aceb6c1.pmf_nonneg b hb.le _)
      simp only [hP] at h1 h2 ⊢
      nlinarith
  -- the difference series
  set T : ℕ → ℝ := fun k => P lam k * f k - P b k * f k with hT
  have sT : Summable T := sL.sub sB
  have sTa : Summable (fun k => |T k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      (((P2M1aceb6c1.pmf_summable lam).mul_right M).add ((P2M1aceb6c1.pmf_summable b).mul_right M))
    simp only [hT, hP]
    have a1 := P2M1aceb6c1.pmf_nonneg lam hl k
    have a2 := P2M1aceb6c1.pmf_nonneg b hb.le k
    calc |Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * f k
          - Real.exp (-b) * b ^ k / (k.factorial : ℝ) * f k|
        ≤ |Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * f k|
          + |Real.exp (-b) * b ^ k / (k.factorial : ℝ) * f k| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonneg a2]
        exact add_le_add (mul_le_mul_of_nonneg_left (hM k) a1)
          (mul_le_mul_of_nonneg_left (hM k) a2)
  have hLHS : poissonExp lam f - poissonExp b f = ∑' k, T k := by
    rw [poissonExp, poissonExp, ← sL.tsum_sub sB]
  have hR1 : poissonExp lam (fun w => |shiftL f w|) = ∑' k, P lam k * |f (k + 1)| := by
    rfl
  have hR2 : poissonExp b (fun w => |f w|) =
      P b 0 * |f 0| + ∑' k, P b (k + 1) * |f (k + 1)| := by
    rw [poissonExp, sBa.tsum_eq_zero_add]
  have sBa1 : Summable (fun k => P b (k + 1) * |f (k + 1)|) :=
    (summable_nat_add_iff 1).mpr sBa
  rw [hLHS, hR1, hR2]
  calc |∑' k, T k| ≤ ∑' k, |T k| := by
        have := norm_tsum_le_tsum_norm (f := T) (by simpa [Real.norm_eq_abs] using sTa)
        simpa [Real.norm_eq_abs] using this
    _ = |T 0| + ∑' k, |T (k + 1)| := sTa.tsum_eq_zero_add
    _ ≤ (lam - b) * (P b 0 * |f 0|) +
          ∑' k, (lam - b) * (P lam k * |f (k + 1)| + P b (k + 1) * |f (k + 1)|) := by
        apply add_le_add
        · simp only [hT]
          rw [← sub_mul, abs_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right key0 (abs_nonneg _)
        · refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff 1).mpr sTa)
            ((sLa.add sBa1).mul_left (lam - b))
          simp only [hT]
          rw [← sub_mul, abs_mul]
          have := mul_le_mul_of_nonneg_right (keyS k) (abs_nonneg (f (k + 1)))
          linarith
    _ = (lam - b) * (∑' k, P lam k * |f (k + 1)| +
          (P b 0 * |f 0| + ∑' k, P b (k + 1) * |f (k + 1)|)) := by
        rw [tsum_mul_left, sLa.tsum_add sBa1]
        ring
