-- Prove2me | solution 1 for TaoFivePrimes.mertens_tail_le_partial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-24T14:29:48.50701+00:00
-- url     : https://prove2.me/submissions/e31cc9a4-f468-41b4-af86-ff5053d99fed

/-
`TaoFivePrimes.mertens_tail_le_partial_sum`

Mertens' tail `Σ_p (log (1 - 1/p) + 1/p)` is a convergent series of *negative*
terms whose value is `B₁ - γ`.  This file proves that it is dominated by *every*
finite partial sum of it:

  `Σ_p (log (1 - 1/p) + 1/p) ≤ Σ_{p ≤ x} (log (1 - 1/p) + 1/p)`.

This is the elementary half of the decomposition of
`TaoFivePrimes.rosser_schoenfeld_product_log_bound_large`: there the analytic
half (Rosser–Schoenfeld (1962), (8.9)) supplies the *strict* upper bound for
`Σ_{p ≤ x} 1/p`, and this lemma removes the constant `B₁ - γ` from the
comparison without any numerical approximation of Mertens' constant.

The only analytic input is the elementary bound `|log (1 - u) + u| ≤ u²/(1 - u)`
for `0 < u < 1`; it gives `|log (1 - 1/p) + 1/p| ≤ 1/(p(p-1)) ≤ 2/p²`, so the
series is dominated by the convergent series `Σ 2/p²`.
-/
import Mathlib

noncomputable section

/-- The summand of Mertens' tail: `log (1 - 1/n) + 1/n`. -/
private def mTail (n : ℕ) : ℝ := Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)

/-- The same summand, extended by zero off the primes. -/
private def mTailOnPrimes (n : ℕ) : ℝ := {m : ℕ | Nat.Prime m}.indicator mTail n

/-- For a series of non-positive reals, every finite partial sum dominates the
total sum. -/
private lemma tsum_le_finset_sum_of_nonpos {ι : Type*} (f : ι → ℝ) (hf : Summable f)
    (hnp : ∀ i, f i ≤ 0) (s : Finset ι) : (∑' i, f i) ≤ ∑ i ∈ s, f i := by
  have h := hf.neg.sum_le_tsum s (fun i _ => neg_nonneg.mpr (hnp i))
  simp only [Finset.sum_neg_distrib, tsum_neg] at h
  linarith

/-- `log (1 - 1/n) + 1/n ≤ 0` for every prime `n`, since `log (1 - u) ≤ -u`. -/
private lemma mTail_nonpos {n : ℕ} (hn : Nat.Prime n) : mTail n ≤ 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
  have hlt : 1 / (n : ℝ) < 1 := by
    rw [div_lt_one hnpos]
    exact_mod_cast hn.one_lt
  have hpos : 0 < 1 - 1 / (n : ℝ) := by linarith
  have hlog : Real.log (1 - 1 / (n : ℝ)) ≤ -(1 / (n : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos hpos
    have h' : (1 : ℝ) - 1 / (n : ℝ) - 1 = -(1 / (n : ℝ)) := by ring
    rw [h'] at h
    exact h
  simp only [mTail]
  linarith

/-- The elementary estimate `|log (1 - 1/n) + 1/n| ≤ 2/n²` for primes `n`. -/
private lemma mTail_abs_le {n : ℕ} (hn : Nat.Prime n) : |mTail n| ≤ 2 / (n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
  have hxpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hx : |1 / (n : ℝ)| < 1 := by
    rw [abs_of_pos hxpos, div_lt_one hnpos]
    exact_mod_cast hn.one_lt
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  have hexp : |1 / (n : ℝ)| ^ (1 + 1) = |1 / (n : ℝ)| ^ 2 := by norm_num
  rw [hexp, Finset.sum_range_one] at h
  simp only [Nat.cast_zero, zero_add, div_one, pow_one] at h
  rw [abs_of_pos hxpos] at h
  -- `h : |1/n + log (1 - 1/n)| ≤ (1/n)^2 / (1 - 1/n)`
  have hden : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have hlt : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one hnpos]
      exact_mod_cast hn.one_lt
    linarith
  have hb : (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ)) ≤ 2 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hden (pow_pos hnpos 2)]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp
    nlinarith [hn2]
  rw [add_comm (1 / (n : ℝ)) (Real.log (1 - 1 / (n : ℝ)))] at h
  simpa only [mTail] using h.trans hb

/-- `mTailOnPrimes` is non-positive everywhere. -/
private lemma mTailOnPrimes_nonpos (n : ℕ) : mTailOnPrimes n ≤ 0 := by
  simp only [mTailOnPrimes]
  by_cases hn : Nat.Prime n
  · rw [Set.indicator_of_mem (s := {m : ℕ | Nat.Prime m}) hn mTail]
    exact mTail_nonpos hn
  · rw [Set.indicator_of_notMem (s := {m : ℕ | Nat.Prime m}) hn mTail]

/-- The negative of `mTailOnPrimes` is dominated by the summable majorant
`2/n²`. -/
private lemma neg_mTailOnPrimes_le (n : ℕ) : -mTailOnPrimes n ≤ 2 / (n : ℝ) ^ 2 := by
  simp only [mTailOnPrimes]
  by_cases hn : Nat.Prime n
  · rw [Set.indicator_of_mem (s := {m : ℕ | Nat.Prime m}) hn mTail]
    exact (neg_le_abs _).trans (mTail_abs_le hn)
  · rw [Set.indicator_of_notMem (s := {m : ℕ | Nat.Prime m}) hn mTail, neg_zero]
    exact div_nonneg (by norm_num) (sq_nonneg _)

private lemma summable_neg_mTailOnPrimes : Summable fun n : ℕ => -mTailOnPrimes n := by
  have hc : Summable fun n : ℕ => 2 / (n : ℝ) ^ 2 := by
    have h1 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (h1.mul_left 2).congr fun n => by rw [mul_one_div]
  exact Summable.of_nonneg_of_le (fun n => neg_nonneg.mpr (mTailOnPrimes_nonpos n))
    (fun n => neg_mTailOnPrimes_le n) hc

private lemma summable_mTailOnPrimes : Summable mTailOnPrimes := by
  exact summable_neg_mTailOnPrimes.neg.congr fun n => by simp

/-- On `Nat.primesLE ⌊x⌋₊` the extension by zero agrees with `mTail`. -/
private lemma sum_mTailOnPrimes_eq_sum_mTail (x : ℝ) :
    (∑ n ∈ Nat.primesLE ⌊x⌋₊, mTailOnPrimes n) = ∑ n ∈ Nat.primesLE ⌊x⌋₊, mTail n := by
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [mTailOnPrimes]
  rw [Set.indicator_of_mem (s := {m : ℕ | Nat.Prime m}) (Nat.mem_primesLE.mp hn).2 mTail]

theorem solution (x : ℝ) :
    (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
  have key : (∑' p : Nat.Primes, mTail (p : ℕ)) ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, mTail p := by
    have h1 : (∑' p : Nat.Primes, mTail (p : ℕ)) = ∑' n : ℕ, mTailOnPrimes n :=
      tsum_subtype {n : ℕ | Nat.Prime n} mTail
    rw [h1, ← sum_mTailOnPrimes_eq_sum_mTail x]
    exact tsum_le_finset_sum_of_nonpos mTailOnPrimes summable_mTailOnPrimes
      mTailOnPrimes_nonpos _
  simpa only [mTail] using key

end
