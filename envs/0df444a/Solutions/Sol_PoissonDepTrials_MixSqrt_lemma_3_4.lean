-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:09:14.68906+00:00
-- url     : https://prove2.me/submissions/7563b5a0-462d-48c5-9e08-d54fa75e3cd2

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

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

end A03F915D

open PoissonDepTrials.MixSqrt in
theorem solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤ 6 * M * min (1 / Real.sqrt lam) 1 := by
  intro w hw
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  obtain ⟨hrec, htail⟩ := A03F915D.aux lam hlam h M hM
  have hP := A03F915D.abs_poissonExp_le lam hlam h M hM
  have hg : ∀ k, |h k - poissonExp lam h| ≤ 2 * M := fun k => by
    calc |h k - poissonExp lam h| ≤ |h k| + |poissonExp lam h| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM k]
  have hT := A03F915D.tail_bound lam hlam h M hM0 hg htail
  have hH := A03F915D.head_bound lam hlam h M hM0 hg hrec
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
