-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:27:27.320984+00:00
-- url     : https://prove2.me/submissions/8c87cb28-c9d8-4777-80c0-24305db15049

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

set_option autoImplicit false

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
theorem P2M1aceb6c1.lemma_5_2 (lam b : ℝ) (hb : 0 < b) (hbl : b ≤ lam) (f : ℕ → ℝ) (M : ℝ)
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

namespace P2M419

open PoissonDepTrials.SecondOrder

lemma pmf_hasSum (t : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-t) * t ^ k / (k.factorial : ℝ)) 1 := by
  have hE : HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have e : (fun k : ℕ => Real.exp (-t) * t ^ k / (k.factorial : ℝ)) =
      fun k => Real.exp (-t) * (t ^ k / (k.factorial : ℝ)) := by
    funext k; ring
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  rw [e, ← h2]
  exact hE.mul_left _

lemma poissonExp_abs_le (t : ℝ) (ht : 0 ≤ t) (f : ℕ → ℝ) (B : ℝ) (hf : ∀ k, |f k| ≤ B) :
    |poissonExp t f| ≤ B := by
  have hs := (pmf_hasSum t).mul_right B
  rw [one_mul] at hs
  unfold poissonExp
  have := tsum_of_norm_bounded (f := fun k => Real.exp (-t) * t ^ k / (k.factorial : ℝ) * f k) hs (fun k => by
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-t) * t ^ k / (k.factorial : ℝ))]
    exact mul_le_mul_of_nonneg_left (hf k) (by positivity))
  rwa [Real.norm_eq_abs] at this

lemma delta_stein (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) :
    ∀ w : ℕ, 1 ≤ w → delta (stein lam h) w =
      -lam⁻¹ * (h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w) := by
  intro w hw
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  have hl : lam ≠ 0 := hlam.ne'
  unfold delta stein
  rw [Finset.sum_range_succ (n := m + 1)]
  have e1 : m + 1 + 1 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1, e2, Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  set A := ∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)
  rw [pow_succ, pow_succ]
  field_simp
  ring

lemma stein_tail (lam : ℝ) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) (w : ℕ) :
    stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ) := by
  have hE : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp lam
  have hs : Summable (fun k : ℕ => h k * (lam ^ k / (k.factorial : ℝ))) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((hE.summable.norm).mul_left M))
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM k) (abs_nonneg _)
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

lemma aprime_bound (lam : ℝ) (hlam : 0 < lam) : ∀ m : ℕ,
    0 ≤ ∑ k ∈ Finset.range (m + 1), (m.factorial : ℝ) * lam ^ k / (k.factorial : ℝ) ∧
    (lam - m) * ∑ k ∈ Finset.range (m + 1), (m.factorial : ℝ) * lam ^ k / (k.factorial : ℝ) ≤
      lam ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
    obtain ⟨h0, h1⟩ := aprime_bound lam hlam m
    have hrec : ∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).factorial : ℝ) * lam ^ k / (k.factorial : ℝ)
        = ((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1), (m.factorial : ℝ) * lam ^ k / (k.factorial : ℝ)
          + lam ^ (m + 1) := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.factorial_succ]; push_cast; ring
      · have : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
        field_simp
    rw [hrec]
    have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hL : (0 : ℝ) ≤ lam ^ (m + 1) := by positivity
    refine ⟨by positivity, ?_⟩
    have h2 := mul_le_mul_of_nonneg_left h1 hm
    have h3 : lam ^ (m + 1 + 1) = lam ^ (m + 1) * lam := pow_succ _ _
    push_cast
    rw [h3]
    nlinarith

/-- `|(v - λ) S(v)| ≤ 2G` for `v = m + 1 ≥ 1`, where `|h k - 𝒫h| ≤ G`. -/
lemma vS_bound (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M)
    (G : ℝ) (hG : ∀ k, |h k - poissonExp lam h| ≤ G) (m : ℕ) :
    |((m : ℝ) + 1 - lam) * stein lam h (m + 1)| ≤ 2 * G := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  have hL : 0 < lam ^ (m + 1) := by positivity
  have hmf : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  rcases le_or_gt ((m : ℝ) + 1) lam with hc | hc
  · -- low case: finite sum
    obtain ⟨hA0, hA1⟩ := aprime_bound lam hlam m
    set A := ∑ k ∈ Finset.range (m + 1), (m.factorial : ℝ) * lam ^ k / (k.factorial : ℝ) with hAdef
    have hS : stein lam h (m + 1) = -((m.factorial : ℝ) * (lam ^ (m + 1))⁻¹ *
        ∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)) := by
      simp [stein]
    have hsum : (m.factorial : ℝ) *
        |∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)| ≤ G * A := by
      have h1 : |∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)| ≤
          ∑ k ∈ Finset.range (m + 1), G * (lam ^ k / (k.factorial : ℝ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [mul_div_assoc, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ k / (k.factorial : ℝ))]
        exact mul_le_mul_of_nonneg_right (hG k) (by positivity)
      have h2 : (m.factorial : ℝ) * ∑ k ∈ Finset.range (m + 1), G * (lam ^ k / (k.factorial : ℝ)) = G * A := by
        rw [hAdef, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      calc _ ≤ (m.factorial : ℝ) * ∑ k ∈ Finset.range (m + 1), G * (lam ^ k / (k.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hmf.le
        _ = G * A := h2
    have habsS : |stein lam h (m + 1)| * lam ^ (m + 1) ≤ G * A := by
      rw [hS, abs_neg, abs_mul, abs_mul, abs_of_pos hmf, abs_of_pos (inv_pos.mpr hL)]
      calc (m.factorial : ℝ) * (lam ^ (m + 1))⁻¹ *
            |∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)| *
            lam ^ (m + 1)
          = (m.factorial : ℝ) *
            |∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)| := by
            field_simp
        _ ≤ G * A := hsum
    have hSabs0 := abs_nonneg (stein lam h (m + 1))
    rw [abs_mul, abs_of_nonpos (by linarith : (m : ℝ) + 1 - lam ≤ 0)]
    -- (lam - m - 1) |S| ≤ (lam - m) |S| ≤ G
    have key : (lam - m) * (|stein lam h (m + 1)| * lam ^ (m + 1)) ≤ G * lam ^ (m + 1) := by
      calc (lam - m) * (|stein lam h (m + 1)| * lam ^ (m + 1)) ≤ (lam - m) * (G * A) :=
            mul_le_mul_of_nonneg_left habsS (by linarith)
        _ = G * ((lam - m) * A) := by ring
        _ ≤ G * lam ^ (m + 1) := mul_le_mul_of_nonneg_left hA1 hG0
    have key2 : (lam - m) * |stein lam h (m + 1)| ≤ G := by
      have := key
      rw [← mul_assoc] at this
      exact le_of_mul_le_mul_right this hL
    nlinarith
  · -- high case: tail
    set v : ℝ := (m : ℝ) + 1 with hv
    have hv1 : 1 ≤ v := by simp [hv]
    set r : ℝ := lam / (v + 1) with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
    set c : ℝ := G * (lam ^ (m + 1) / ((m + 1).factorial : ℝ)) with hc
    have hgeo : HasSum (fun k : ℕ => c * r ^ k) (c * (1 - r)⁻¹) :=
      (hasSum_geometric_of_lt_one hr0 hr1).mul_left c
    have hterm : ∀ k : ℕ, ‖(h (k + (m + 1)) - poissonExp lam h) * lam ^ (k + (m + 1)) /
        ((k + (m + 1)).factorial : ℝ)‖ ≤ c * r ^ k := by
      intro k
      have hfac : ((m + 1).factorial : ℝ) * ((m : ℝ) + 1 + 1) ^ k ≤ ((k + (m + 1)).factorial : ℝ) := by
        have := Nat.factorial_mul_pow_le_factorial (m := m + 1) (n := k)
        rw [add_comm (m + 1) k] at this
        exact_mod_cast this
      have hf1 : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
      have hf2 : (0 : ℝ) < ((k + (m + 1)).factorial : ℝ) := by positivity
      rw [Real.norm_eq_abs, mul_div_assoc, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ))]
      have hq : lam ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ) ≤
          lam ^ (m + 1) / ((m + 1).factorial : ℝ) * r ^ k := by
        rw [hr, div_pow, pow_add, div_le_iff₀ hf2]
        have hpos : (0 : ℝ) < (v + 1) ^ k := by positivity
        rw [hv]
        field_simp
        have : lam ^ k * lam ^ (m + 1) * (((m + 1).factorial : ℝ) * ((m : ℝ) + 1 + 1) ^ k) ≤
            lam ^ k * lam ^ (m + 1) * ((k + (m + 1)).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
        nlinarith
      calc |h (k + (m + 1)) - poissonExp lam h| *
            (lam ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ))
          ≤ G * (lam ^ (m + 1) / ((m + 1).factorial : ℝ) * r ^ k) :=
            mul_le_mul (hG _) hq (by positivity) hG0
        _ = c * r ^ k := by rw [hc]; ring
    have hT := tsum_of_norm_bounded hgeo hterm
    rw [Real.norm_eq_abs] at hT
    have hS := stein_tail lam h M hM (m + 1)
    rw [Nat.add_sub_cancel] at hS
    have hSabs : |stein lam h (m + 1)| ≤ G / v * (1 - r)⁻¹ := by
      rw [hS, abs_mul, abs_mul, abs_of_pos hmf, abs_of_pos (inv_pos.mpr hL)]
      calc (m.factorial : ℝ) * (lam ^ (m + 1))⁻¹ * |∑' k : ℕ, (h (k + (m + 1)) - poissonExp lam h) *
              lam ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ)|
          ≤ (m.factorial : ℝ) * (lam ^ (m + 1))⁻¹ * (c * (1 - r)⁻¹) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = G / v * (1 - r)⁻¹ := by
            rw [hc, hv, Nat.factorial_succ]
            push_cast
            field_simp
    have h1r : (1 - r)⁻¹ = (v + 1) / (v + 1 - lam) := by
      rw [hr]
      have : v + 1 - lam ≠ 0 := by linarith
      have : v + 1 ≠ 0 := by linarith
      field_simp
    rw [h1r] at hSabs
    have hpos : 0 < v + 1 - lam := by linarith
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < v - lam)]
    have hSa0 := abs_nonneg (stein lam h (m + 1))
    -- (v - lam) |S| ≤ (v+1-lam) |S| ≤ G (v+1)/v ≤ 2G
    have e3 : (v + 1 - lam) * (G / v * ((v + 1) / (v + 1 - lam))) = G * (v + 1) / v := by
      field_simp
    have h4 : (v + 1 - lam) * |stein lam h (m + 1)| ≤ G * (v + 1) / v := by
      rw [← e3]; exact mul_le_mul_of_nonneg_left hSabs hpos.le
    have h5 : G * (v + 1) / v ≤ 2 * G := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith

/-- K0 with constant 6: `|U_λ h(w)| ≤ 6M/λ`. -/
theorem stU_abs_le (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M)
    (w : ℕ) : |stU lam h w| ≤ 6 * M / lam := by
  have hP : |poissonExp lam h| ≤ M := poissonExp_abs_le lam hlam.le h M hM
  have hG : ∀ k, |h k - poissonExp lam h| ≤ 2 * M := fun k =>
    (abs_sub _ _).trans (by linarith [hM k])
  have hd := delta_stein lam hlam h (w + 1) (by omega)
  have hv := vS_bound lam hlam h M hM (2 * M) hG w
  unfold stU
  rw [hd]
  push_cast
  rw [abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hlam), div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hlam).le
  calc |h (w + 1) - poissonExp lam h - ((w : ℝ) + 1 - lam) * stein lam h (w + 1)|
      ≤ |h (w + 1) - poissonExp lam h| + |((w : ℝ) + 1 - lam) * stein lam h (w + 1)| :=
        abs_sub _ _
    _ ≤ 2 * M + 2 * (2 * M) := add_le_add (hG _) hv
    _ = 6 * M := by ring

end P2M419

namespace P2M419

open PoissonDepTrials.SecondOrder

lemma stein_eq (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (w : ℕ) :
    (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h := by
  have hl0 : lam ≠ 0 := hlam.ne'
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

lemma W_split {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (hi : i ∈ Finset.Icc 1 n) (ω : Ω) :
    W n X ω = Wi n X i ω + X i ω := by
  unfold W Wi
  rw [Finset.filter_ne', Finset.sum_erase_add _ _ hi]

lemma W_le {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hω : ∀ i, X i ω ≤ 1) :
    W n X ω ≤ n := by
  unfold W
  calc ∑ i ∈ Finset.Icc 1 n, X i ω ≤ ∑ i ∈ Finset.Icc 1 n, 1 := Finset.sum_le_sum fun i _ => hω i
    _ = n := by simp

lemma Wi_le_W {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) : Wi n X i ω ≤ W n X ω :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma integ_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (V : Ω → ℕ) (hV : Measurable V) (N : ℕ) (hVN : ∀ᵐ ω ∂P, V ω ≤ N) (g : ℕ → ℝ) :
    Integrable (fun ω => g (V ω)) P := by
  refine Integrable.of_bound (C := ∑ k ∈ Finset.range (N + 1), |g k|) ?_ ?_
  · exact ((measurable_from_nat (f := g)).comp hV).aestronglyMeasurable
  · filter_upwards [hVN] with ω hω
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun k => |g k|) (fun k _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))

lemma integ_mul_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A V : Ω → ℕ) (hA : Measurable A) (hV : Measurable V) (N : ℕ)
    (hAV : ∀ᵐ ω ∂P, A ω ≤ 1 ∧ V ω ≤ N) (g : ℕ → ℝ) :
    Integrable (fun ω => (A ω : ℝ) * g (V ω)) P := by
  refine Integrable.of_bound (C := ∑ k ∈ Finset.range (N + 1), |g k|) ?_ ?_
  · exact (((measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp hA).mul
      ((measurable_from_nat (f := g)).comp hV)).aestronglyMeasurable
  · filter_upwards [hAV] with ω hω
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    have h1 : (A ω : ℝ) ≤ 1 := by exact_mod_cast hω.1
    have h2 : |g (V ω)| ≤ ∑ k ∈ Finset.range (N + 1), |g k| :=
      Finset.single_le_sum (f := fun k => |g k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have h3 : 0 ≤ |g (V ω)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ (A ω : ℝ) := Nat.cast_nonneg _
    nlinarith

lemma indep_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hmeas : ∀ i, Measurable (X i))
    (hind : iIndepFun (fun i => X i) P) (i : ℕ) (g : ℕ → ℝ) :
    ∫ ω, (X i ω : ℝ) * g (Wi n X i ω) ∂P =
      (∫ ω, (X i ω : ℝ) ∂P) * ∫ ω, g (Wi n X i ω) ∂P := by
  have hd : Disjoint ({i} : Finset ℕ) ((Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i)) := by
    rw [Finset.disjoint_singleton_left]; simp
  have hI := hind.indepFun_finset {i} ((Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i)) hd hmeas
  have mφ : Measurable (fun f : ({i} : Finset ℕ) → ℕ =>
      ((f ⟨i, Finset.mem_singleton_self i⟩ : ℕ) : ℝ)) :=
    (measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply _)
  have mψ : Measurable (fun f : ((Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i)) → ℕ =>
      g (∑ j, f j)) :=
    (measurable_from_nat (f := g)).comp (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
  have hI2 := hI.comp mφ mψ
  have e2 : (fun f : ((Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i)) → ℕ => g (∑ j, f j)) ∘
      (fun a (j : ((Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i))) => X j a) =
        fun ω => g (Wi n X i ω) := by
    funext ω
    simp only [Function.comp, Wi]
    rw [Finset.sum_coe_sort _ (fun j => X j ω)]
  rw [e2] at hI2
  exact hI2.integral_fun_mul_eq_mul_integral
    ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp (hmeas i)).aestronglyMeasurable
    (((measurable_from_nat (f := g)).comp
      (Finset.measurable_sum _ fun j _ => hmeas j))).aestronglyMeasurable

lemma integral_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hmeas : ∀ i, Measurable (X i)) (i : ℕ) (hle : ∀ᵐ ω ∂P, X i ω ≤ 1) :
    ∫ ω, (X i ω : ℝ) ∂P = prob P X i := by
  have hs : MeasurableSet {ω | X i ω = 1} := (hmeas i) (measurableSet_singleton 1)
  have hae : (fun ω => (X i ω : ℝ)) =ᵐ[P] Set.indicator {ω | X i ω = 1} (1 : Ω → ℝ) := by
    filter_upwards [hle] with ω hω
    by_cases h1 : X i ω = 1
    · simp [Set.indicator, h1]
    · have h0 : X i ω = 0 := by omega
      simp [Set.indicator, h0]
  rw [integral_congr_ae hae, integral_indicator_one hs]
  rfl

theorem identity_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (hlam : 0 < lam P n X) (h : ℕ → ℝ) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h -
      ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P := by
  set L := lam P n X with hL
  set S := stein L h with hSdef
  set U := stU L h with hUdef
  have hmeas := hX.1
  have hgood : ∀ᵐ ω ∂P, ∀ i, X i ω ≤ 1 := ae_all_iff.2 hX.2.2
  have mW : Measurable (W n X) := by
    unfold W; exact Finset.measurable_sum _ fun i _ => hmeas i
  have mWi : ∀ i, Measurable (Wi n X i) := fun i => by
    unfold Wi; exact Finset.measurable_sum _ fun j _ => hmeas j
  have bW : ∀ᵐ ω ∂P, W n X ω ≤ n := hgood.mono fun ω hω => W_le n X ω hω
  have bWi : ∀ i, ∀ᵐ ω ∂P, Wi n X i ω ≤ n := fun i =>
    hgood.mono fun ω hω => (Wi_le_W n X i ω).trans (W_le n X ω hω)
  have iW : ∀ g : ℕ → ℝ, Integrable (fun ω => g (W n X ω)) P := fun g => integ_comp P _ mW n bW g
  have iWi : ∀ i (g : ℕ → ℝ), Integrable (fun ω => g (Wi n X i ω)) P := fun i g =>
    integ_comp P _ (mWi i) n (bWi i) g
  have iXWi : ∀ i (g : ℕ → ℝ), Integrable (fun ω => (X i ω : ℝ) * g (Wi n X i ω)) P :=
    fun i g => integ_mul_comp P _ _ (hmeas i) (mWi i) n
      ((hgood.and (bWi i)).mono fun ω hω => ⟨hω.1 i, hω.2⟩) g
  have hEX : ∀ i, ∫ ω, (X i ω : ℝ) ∂P = prob P X i := fun i =>
    integral_X P X hmeas i (hX.2.2 i)
  -- I1: E h(W) = E[W S(W)] - L E S(W+1) + 𝒫h
  have I1 : ∫ ω, h (W n X ω) ∂P = ∫ ω, (W n X ω : ℝ) * S (W n X ω) ∂P -
      L * ∫ ω, S (W n X ω + 1) ∂P + poissonExp L h := by
    have e : (fun ω => h (W n X ω)) = fun ω => ((W n X ω : ℝ) * S (W n X ω) -
        L * S (W n X ω + 1)) + poissonExp L h := by
      funext ω
      have := stein_eq L hlam h (W n X ω)
      rw [hSdef]; linarith
    rw [e, integral_add _ (integrable_const _), integral_sub, integral_const_mul, integral_const]
    · simp
    · exact iW (fun k => (k : ℝ) * S k)
    · exact (iW (fun k => S (k + 1))).const_mul L
    · exact (iW (fun k => (k : ℝ) * S k)).sub ((iW (fun k => S (k + 1))).const_mul L)
  -- I2: E[W S(W)] = Σ_i E[X_i S(W^(i)+1)]
  have I2 : ∫ ω, (W n X ω : ℝ) * S (W n X ω) ∂P =
      ∑ i ∈ Finset.Icc 1 n, ∫ ω, (X i ω : ℝ) * S (Wi n X i ω + 1) ∂P := by
    rw [← integral_finsetSum _ fun i _ => iXWi i (fun k => S (k + 1))]
    refine integral_congr_ae (hgood.mono fun ω hω => ?_)
    simp only
    have hc : (W n X ω : ℝ) = ∑ i ∈ Finset.Icc 1 n, (X i ω : ℝ) := by
      unfold W; push_cast; rfl
    rw [hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hs := W_split n X i hi ω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hω i) with h0 | h1
    · simp [h0]
    · rw [hs, h1]
  -- I4: E S(W+1) = E S(W^(i)+1) + E[X_i U(W^(i))]
  have I4 : ∀ i ∈ Finset.Icc 1 n, ∫ ω, S (W n X ω + 1) ∂P =
      ∫ ω, S (Wi n X i ω + 1) ∂P + ∫ ω, (X i ω : ℝ) * U (Wi n X i ω) ∂P := by
    intro i hi
    rw [← integral_add (iWi i (fun k => S (k + 1))) (iXWi i U)]
    refine integral_congr_ae (hgood.mono fun ω hω => ?_)
    simp only
    have hs := W_split n X i hi ω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hω i) with h0 | h1
    · simp [hs, h0]
    · rw [hs, h1, hUdef]
      simp only [stU, delta, Nat.cast_one, one_mul]
      rw [hSdef]
      ring_nf
  have I3 : ∀ i, ∫ ω, (X i ω : ℝ) * S (Wi n X i ω + 1) ∂P =
      prob P X i * ∫ ω, S (Wi n X i ω + 1) ∂P := fun i => by
    rw [indep_mul P n X hmeas hind i (fun k => S (k + 1)), hEX]
  have I5 : ∀ i, ∫ ω, (X i ω : ℝ) * U (Wi n X i ω) ∂P =
      prob P X i * ∫ ω, U (Wi n X i ω) ∂P := fun i => by
    rw [indep_mul P n X hmeas hind i U, hEX]
  have hLs : L * ∫ ω, S (W n X ω + 1) ∂P = ∑ i ∈ Finset.Icc 1 n, prob P X i *
      (∫ ω, S (Wi n X i ω + 1) ∂P + prob P X i * ∫ ω, U (Wi n X i ω) ∂P) := by
    rw [hL, lam, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [I4 i hi, I5 i]
  rw [I1, I2, hLs]
  simp_rw [I3]
  have hk : ∀ i ∈ Finset.Icc 1 n, prob P X i * ∫ ω, S (Wi n X i ω + 1) ∂P -
      prob P X i * (∫ ω, S (Wi n X i ω + 1) ∂P + prob P X i * ∫ ω, U (Wi n X i ω) ∂P) =
      -(prob P X i ^ 2 * ∫ ω, U (Wi n X i ω) ∂P) := fun i _ => by ring
  have hsum := Finset.sum_congr rfl hk
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
  linarith

lemma drop_trial {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (i : ℕ) :
    IsBernoulliTrials P n (Function.update X i 0) ∧
    iIndepFun (fun k => Function.update X i 0 k) P ∧
    lam P n (Function.update X i 0) = lamExcept P n X i ∧
    W n (Function.update X i 0) = Wi n X i ∧
    (∀ k, prob P (Function.update X i 0) k = if k = i then 0 else prob P X k) := by
  have hprob : ∀ k, prob P (Function.update X i 0) k = if k = i then 0 else prob P X k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [prob]
    · simp [prob, hk]
  refine ⟨⟨fun k => ?_, fun k hk => ?_, fun k => ?_⟩, ?_, ?_, ?_, hprob⟩
  · by_cases hk : k = i
    · subst hk; simp only [Function.update_self]; exact measurable_const
    · rw [Function.update_of_ne hk]; exact hX.1 k
  · by_cases hk' : k = i
    · subst hk'; simp
    · rw [Function.update_of_ne hk']; exact hX.2.1 k hk
  · by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; exact hX.2.2 k
  · have hc := hind.comp (fun k => if k = i then (fun _ : ℕ => (0 : ℕ)) else id)
      (fun k => measurable_from_nat)
    convert hc using 1
    funext k ω
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  · unfold lam lamExcept
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hprob j]
    by_cases hj : j = i <;> simp [hj]
  · funext ω
    unfold W Wi
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

end P2M419

namespace P2M419

open PoissonDepTrials.SecondOrder

lemma abs_integral_le_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (C : ℝ) (hf : ∀ ω, |f ω| ≤ C) :
    |∫ ω, f ω ∂P| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := C)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf ω)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma key_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2) (hlam : 0 < lam P n X)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
    |poissonExp (lam P n X) (stU (lam P n X) h) - ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P| ≤
      12 * prob P X i / lam P n X + ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
        prob P X j ^ 2 * (36 / (lam P n X * lamExcept P n X i)) := by
  have hp0 : ∀ k, 0 ≤ prob P X k := fun k => measureReal_nonneg
  have hb : lamExcept P n X i = lam P n X - prob P X i := by
    unfold lamExcept lam; rw [Finset.filter_ne', Finset.sum_erase_eq_sub hi]
  have hb0 : 0 < lamExcept P n X i := by rw [hb]; linarith [hpbar i hi]
  obtain ⟨hX', hind', hlam', hW', hprob'⟩ := drop_trial P n X hX hind i
  have hid := identity_5_8 P n (Function.update X i 0) hX' hind' (by rw [hlam']; exact hb0)
    (stU (lam P n X) h)
  rw [hlam', hW'] at hid
  rw [hid]
  have hLb : lam P n X - lamExcept P n X i = prob P X i := by rw [hb]; ring
  generalize lam P n X = L at *
  generalize lamExcept P n X i = b at *
  have hUb : ∀ w, |stU L h w| ≤ 6 / L := fun w => by
    have := stU_abs_le L hlam h 1 hh w
    simpa using this
  have h52 := P2M1aceb6c1.lemma_5_2 L b hb0 (by linarith [hp0 i]) (stU L h) (6 / L) hUb
  have hPL : poissonExp L (fun w => |shiftL (stU L h) w|) ≤ 6 / L :=
    (le_abs_self _).trans (poissonExp_abs_le L hlam.le _ _ fun k => by
      simp only [abs_abs, shiftL]; exact hUb (k + 1))
  have hPb : poissonExp b (fun w => |stU L h w|) ≤ 6 / L :=
    (le_abs_self _).trans (poissonExp_abs_le b hb0.le _ _ fun k => by
      simp only [abs_abs]; exact hUb k)
  have hdiff : |poissonExp L (stU L h) - poissonExp b (stU L h)| ≤ 12 * prob P X i / L := by
    calc _ ≤ (L - b) * (poissonExp L (fun w => |shiftL (stU L h) w|) +
            poissonExp b (fun w => |stU L h w|)) := h52
      _ ≤ prob P X i * (6 / L + 6 / L) := by
          rw [hLb]; exact mul_le_mul_of_nonneg_left (add_le_add hPL hPb) (hp0 i)
      _ = 12 * prob P X i / L := by ring
  have hUU : ∀ v, |stU b (stU L h) v| ≤ 36 / (L * b) := fun v => by
    have := stU_abs_le b hb0 (stU L h) (6 / L) hUb v
    calc _ ≤ 6 * (6 / L) / b := this
      _ = 36 / (L * b) := by field_simp; ring
  have hsum : |∑ j ∈ Finset.Icc 1 n, prob P (Function.update X i 0) j ^ 2 *
      ∫ ω, stU b (stU L h) (Wi n (Function.update X i 0) j ω) ∂P| ≤
      ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i), prob P X j ^ 2 * (36 / (L * b)) := by
    rw [Finset.sum_filter]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [hprob' j]
    by_cases hj : j = i
    · simp [hj]
    · rw [if_neg hj, if_pos hj, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (abs_integral_le_const P _ _ fun ω => hUU _) (sq_nonneg _)
  have e : poissonExp L (stU L h) - (poissonExp b (stU L h) -
      ∑ j ∈ Finset.Icc 1 n, prob P (Function.update X i 0) j ^ 2 *
        ∫ ω, stU b (stU L h) (Wi n (Function.update X i 0) j ω) ∂P) =
      (poissonExp L (stU L h) - poissonExp b (stU L h)) +
      ∑ j ∈ Finset.Icc 1 n, prob P (Function.update X i 0) j ^ 2 *
        ∫ ω, stU b (stU L h) (Wi n (Function.update X i 0) j ω) ∂P := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add hdiff hsum)

theorem bound_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2) (hlam : 0 < lam P n X) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      24 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 +
        96 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i := by
  have hp0 : ∀ k, 0 ≤ prob P X k := fun k => measureReal_nonneg
  have hbpos : ∀ i ∈ Finset.Icc 1 n, 0 < lamExcept P n X i := fun i hi => by
    have hb : lamExcept P n X i = lam P n X - prob P X i := by
      unfold lamExcept lam; rw [Finset.filter_ne', Finset.sum_erase_eq_sub hi]
    rw [hb]; linarith [hpbar i hi]
  have hkey := key_bound P n X hX hind h hh hpbar hlam
  have hid := identity_5_8 P n X hX hind hlam h
  rw [hid]
  have hexpr : poissonExp (lam P n X) h - ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 *
        ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P - poissonExp (lam P n X) h +
      (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h) =
      ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * (poissonExp (lam P n X) (stU (lam P n X) h) -
        ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P) := by
    rw [Finset.sum_mul]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hexpr]
  generalize hLd : lam P n X = L at *
  have hfinal : ∀ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * (12 * prob P X i / L +
      ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
        prob P X j ^ 2 * (36 / (L * lamExcept P n X i))) ≤
      24 * L⁻¹ * prob P X i ^ 3 + 96 * L⁻¹ * ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
        prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i := by
    intro i hi
    have hb0 := hbpos i hi
    have hpi := hp0 i
    rw [mul_add]
    have t1 : prob P X i ^ 2 * (12 * prob P X i / L) ≤ 24 * L⁻¹ * prob P X i ^ 3 := by
      have h0 : 0 ≤ L⁻¹ * prob P X i ^ 3 := by positivity
      have e1 : prob P X i ^ 2 * (12 * prob P X i / L) = 12 * (L⁻¹ * prob P X i ^ 3) := by
        rw [div_eq_mul_inv]; ring
      rw [e1]; nlinarith
    have t2 : prob P X i ^ 2 * ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
        prob P X j ^ 2 * (36 / (L * lamExcept P n X i)) ≤
        96 * L⁻¹ * ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
          prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hpj := hp0 j
      have h0 : 0 ≤ L⁻¹ * (prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i) := by positivity
      have e1 : prob P X i ^ 2 * (prob P X j ^ 2 * (36 / (L * lamExcept P n X i))) =
          36 * (L⁻¹ * (prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
      have e2 : 96 * L⁻¹ * (prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i) =
          96 * (L⁻¹ * (prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i)) := by ring
      rw [e1, e2]; linarith
    linarith
  calc |∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * (poissonExp L (stU L h) -
          ∫ ω, stU L h (Wi n X i ω) ∂P)|
      ≤ ∑ i ∈ Finset.Icc 1 n, |prob P X i ^ 2 * (poissonExp L (stU L h) -
          ∫ ω, stU L h (Wi n X i ω) ∂P)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * (12 * prob P X i / L +
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X j ^ 2 * (36 / (L * lamExcept P n X i))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hkey i hi) (sq_nonneg _)
    _ ≤ ∑ i ∈ Finset.Icc 1 n, (24 * L⁻¹ * prob P X i ^ 3 +
          96 * L⁻¹ * ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i) := Finset.sum_le_sum hfinal
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end P2M419

namespace PDT51

open PoissonDepTrials.SecondOrder

theorem jensen (n : ℕ) (p : ℕ → ℝ) (hp : ∀ i ∈ Finset.Icc 1 n, 0 ≤ p i)
    (hlam : 0 < ∑ i ∈ Finset.Icc 1 n, p i)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, p i ≤ (∑ k ∈ Finset.Icc 1 n, p k) / 2) :
    (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 *
        ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
          p j ^ 2 / ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), p k ≤
      Real.sqrt 2 * (∑ k ∈ Finset.Icc 1 n, p k)⁻¹ * ∑ i ∈ Finset.Icc 1 n, p i ^ 3 := by
  set s := Finset.Icc 1 n with hs
  set S := ∑ k ∈ s, p k with hS
  set T := ∑ i ∈ s, p i ^ 3 with hT
  set Q := ∑ i ∈ s, p i ^ 2 with hQ
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i hi => pow_nonneg (hp i hi) 3
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i hi => sq_nonneg (p i)
  have hCS : ∀ t ⊆ s, (∑ j ∈ t, p j ^ 2) ^ 2 ≤ (∑ j ∈ t, p j) * ∑ j ∈ t, p j ^ 3 := by
    intro t ht
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun j hj => hp j (ht hj))
      (fun j hj => pow_nonneg (hp j (ht hj)) 3) (fun j hj => le_of_eq (by ring))
  set c := Real.sqrt (2 * T / S) with hc
  have hinner : ∀ i ∈ s, (∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k) ≤ c := by
    intro i hi
    set F := s.filter (fun j : ℕ => j ≠ i) with hF
    have hFs : F ⊆ s := Finset.filter_subset _ _
    have hb : ∑ k ∈ F, p k = S - p i := by
      rw [hF, Finset.filter_ne', Finset.sum_erase_eq_sub hi]
    set b := ∑ k ∈ F, p k with hbdef
    have hbS : S ≤ 2 * b := by rw [hb]; linarith [hpbar i hi]
    have hbpos : 0 < b := by linarith
    set A := ∑ j ∈ F, p j ^ 2 with hA
    have hTF : ∑ j ∈ F, p j ^ 3 ≤ T :=
      Finset.sum_le_sum_of_subset_of_nonneg hFs fun j hj _ => pow_nonneg (hp j hj) 3
    have hA2 : A ^ 2 ≤ b * T := by
      calc A ^ 2 ≤ b * ∑ j ∈ F, p j ^ 3 := hCS F hFs
        _ ≤ b * T := mul_le_mul_of_nonneg_left hTF hbpos.le
    rw [← Finset.sum_div]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_div_iff₀ (by positivity) hlam]
    have h1 : A ^ 2 * S ≤ b * T * S := mul_le_mul_of_nonneg_right hA2 hlam.le
    have h2 : b * T * S ≤ b * T * (2 * b) :=
      mul_le_mul_of_nonneg_left hbS (mul_nonneg hbpos.le hT0)
    nlinarith
  have hsum : ∑ i ∈ s, p i ^ 2 * ∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k ≤ Q * c := by
    rw [hQ, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hinner i hi) (sq_nonneg (p i))
  have hQ2 : Q ^ 2 ≤ S * T := hCS s le_rfl
  have hQc : Q * c ≤ Real.sqrt 2 * T := by
    have e1 : Q * c = Real.sqrt (Q ^ 2 * (2 * T / S)) := by
      rw [Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq hQ0]
    have e2 : Real.sqrt 2 * T = Real.sqrt (2 * T ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hT0]
    rw [e1, e2]
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', div_le_iff₀ hlam]
    nlinarith
  have hSinv : 0 ≤ S⁻¹ := inv_nonneg.mpr hlam.le
  calc S⁻¹ * ∑ i ∈ s, p i ^ 2 * ∑ j ∈ s.filter (fun j : ℕ => j ≠ i),
        p j ^ 2 / ∑ k ∈ s.filter (fun k : ℕ => k ≠ i), p k
      ≤ S⁻¹ * (Q * c) := mul_le_mul_of_nonneg_left hsum hSinv
    _ ≤ S⁻¹ * (Real.sqrt 2 * T) := mul_le_mul_of_nonneg_left hQc hSinv
    _ = Real.sqrt 2 * S⁻¹ * T := by ring

theorem poissonExp_zero (h : ℕ → ℝ) : poissonExp 0 h = h 0 := by
  unfold poissonExp
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; simp [zero_pow hk]

/-- The parent, given the conclusion of bound_5_9 (a438ebfc) for `0 < λ`. -/
theorem theorem_5_1_of_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X)
    (h : ℕ → ℝ)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2)
    (hb : 0 < lam P n X →
      |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      24 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 +
        96 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      (24 + 96 * Real.sqrt 2) * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 := by
  have hp0 : ∀ i, 0 ≤ prob P X i := fun i => measureReal_nonneg
  have hlam0 : 0 ≤ lam P n X := Finset.sum_nonneg fun i _ => hp0 i
  rcases hlam0.eq_or_lt with hz | hpos
  · -- λ = 0
    have hpi : ∀ i ∈ Finset.Icc 1 n, prob P X i = 0 := by
      have hs0 : ∑ i ∈ Finset.Icc 1 n, prob P X i = 0 := hz.symm
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp0 i)).1 hs0
    have hXi : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X i ω = 0 := by
      intro i hi
      have hm : P {ω | X i ω = 1} = 0 := by
        have h0 := hpi i hi
        unfold prob at h0
        rwa [measureReal_eq_zero_iff] at h0
      have hne : ∀ᵐ ω ∂P, X i ω ≠ 1 := by
        rw [ae_iff]; simpa using hm
      filter_upwards [hne, hX.2.2 i] with ω h1 h2
      omega
    have hW : ∀ᵐ ω ∂P, W n X ω = 0 := by
      have hall : ∀ᵐ ω ∂P, ∀ i ∈ Finset.Icc 1 n, X i ω = 0 := by
        exact (Filter.eventually_all_finset _).2 hXi
      filter_upwards [hall] with ω hω
      exact Finset.sum_eq_zero hω
    have hint : ∫ ω, h (W n X ω) ∂P = h 0 := by
      have hae : (fun ω => h (W n X ω)) =ᵐ[P] fun _ => h 0 :=
        hW.mono fun ω hω => by simp only [hω]
      rw [integral_congr_ae hae]
      simp
    have hsq : ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hpi i hi]; ring
    rw [← hz, hint, poissonExp_zero, hsq]
    simp
  · have h1 := hb hpos
    have hJ := jensen n (prob P X) (fun i _ => hp0 i) hpos hpbar
    have hrw : ∑ i ∈ Finset.Icc 1 n,
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X i ^ 2 * prob P X j ^ 2 / lamExcept P n X i =
        ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 *
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X j ^ 2 / ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), prob P X k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold lamExcept
      ring
    rw [hrw] at h1
    have hJ' : 96 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 *
          ∑ j ∈ (Finset.Icc 1 n).filter (fun j : ℕ => j ≠ i),
            prob P X j ^ 2 / ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k ≠ i), prob P X k ≤
        96 * (Real.sqrt 2 * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hJ (by norm_num)
    linarith
end PDT51

open MeasureTheory ProbabilityTheory Finset PoissonDepTrials.SecondOrder in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) (hn : 2 ≤ n)
    (hpbar : ∀ i ∈ Finset.Icc 1 n, prob P X i ≤ lam P n X / 2) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h +
        (∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) * poissonExp (lam P n X) (stU (lam P n X) h)| ≤
      (24 + 96 * Real.sqrt 2) * (lam P n X)⁻¹ * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 3 := by
  refine PDT51.theorem_5_1_of_bound P n X hX h hpbar ?_
  intro hlam
  exact P2M419.bound_5_9 P n X hX hind h hh hpbar hlam

