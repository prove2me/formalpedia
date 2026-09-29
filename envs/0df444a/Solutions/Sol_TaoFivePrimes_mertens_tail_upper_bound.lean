-- Prove2me | solution 1 for TaoFivePrimes.mertens_tail_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-27T15:53:05.721994+00:00
-- url     : https://prove2.me/submissions/d66238e2-dbe5-4d9d-be01-010f0b758cbd

/-
`TaoFivePrimes.mertens_tail_upper_bound`

Companion of the already-proved `TaoFivePrimes.mertens_tail_le_partial_sum`
(`c10a0cd0`), which says that the convergent series

    T(inf) = sum'_p (log (1 - 1/p) + 1/p)

of *negative* terms is dominated by every finite partial sum
`T(x) = sum_{p <= x} (log (1 - 1/p) + 1/p)`, i.e. `T(inf) <= T(x)`.

Here we bound the same tail from the other side:

    T(x) <= T(inf) + 1/floor(x)          (1 <= x).

This is the elementary input that every *upper* estimate for the reciprocal
prime sum needs and that the platform did not have.  Indeed, with

    P(x) = prod_{p <= floor x} p/(p-1),

the exact identity `sum_{p<=x} 1/p = log P(x) + T(x)` turns any upper bound for
`log P(x)` into an upper bound for `sum 1/p` only after `T(x)` has been pushed
back down to `T(inf)`, and that is exactly the tail estimate proved here.

The proof is elementary and uses nothing beyond Mathlib:

  * `|log (1 - 1/p) + 1/p| <= 1/(p(p-1))` for primes `p`, from
    `Real.abs_log_sub_add_sum_range_le` at `x = 1/p`, `n = 1`;
  * extension of the summand by zero off the primes, and `tsum_subtype`;
  * `Summable.sum_add_tsum_nat_add` to split the series at `floor x + 1`;
  * the telescoping identity `1/((n+N)(n+N+1)) = 1/(n+N) - 1/(n+N+1)`, summed
    by `Finset.sum_range_sub'` and passed to the limit by
    `hasSum_iff_tendsto_nat_of_nonneg`.

No prime-counting input, no numerical constant, no external quotation.
-/
import Mathlib

noncomputable section

open BigOperators
open Filter

/-- The summand of Mertens' tail: `log (1 - 1/n) + 1/n`. -/
private def mTailU (n : ℕ) : ℝ := Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)

/-- The same summand, extended by zero off the primes. -/
private def mTailUP (n : ℕ) : ℝ := {m : ℕ | Nat.Prime m}.indicator mTailU n

/-- `log (1 - 1/n) + 1/n <= 0` for every prime `n`, since `log (1 - u) <= -u`. -/
private lemma mTailU_nonpos {n : ℕ} (hn : Nat.Prime n) : mTailU n ≤ 0 := by
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
  simp only [mTailU]
  linarith

/-- The elementary estimate `|log (1 - 1/n) + 1/n| <= 1/(n(n-1))`. -/
private lemma mTailU_abs_le {n : ℕ} (hn : Nat.Prime n) :
    |mTailU n| ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
  have hxpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hx : |1 / (n : ℝ)| < 1 := by
    rw [abs_of_pos hxpos, div_lt_one hnpos]
    exact_mod_cast hn.one_lt
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  have hexp : |1 / (n : ℝ)| ^ (1 + 1) = |1 / (n : ℝ)| ^ 2 := by norm_num
  rw [hexp, Finset.sum_range_one] at h
  simp only [Nat.cast_zero, zero_add, div_one, pow_one] at h
  rw [abs_of_pos hxpos] at h
  have hb : (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ)) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hgt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.one_lt
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hn0, hn1]
  rw [add_comm (1 / (n : ℝ)) (Real.log (1 - 1 / (n : ℝ)))] at h
  simpa only [mTailU, hb] using h

/-- `1/(n(n-1)) <= 2/n^2` for primes `n`. -/
private lemma inv_mul_pred_le_two_div_sq {n : ℕ} (hn : Nat.Prime n) :
    1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 / (n : ℝ) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [div_le_div_iff₀ hden (pow_pos hnpos 2)]
  nlinarith

/-- `mTailUP` is non-positive everywhere. -/
private lemma mTailUP_nonpos (n : ℕ) : mTailUP n ≤ 0 := by
  by_cases hn : Nat.Prime n
  · simpa [mTailUP, hn] using mTailU_nonpos hn
  · simp [mTailUP, hn]

/-- `-mTailUP n <= 1/(n(n-1))` for every `n >= 2`; off the primes the left side
is `0` and the right side is non-negative. -/
private lemma neg_mTailUP_le (n : ℕ) (hn : 2 ≤ n) :
    -mTailUP n ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  by_cases hp : Nat.Prime n
  · simpa [mTailUP, hp] using (neg_le_abs (mTailU n)).trans (mTailU_abs_le hp)
  · have hnonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
        have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
        linarith
      exact div_nonneg (by norm_num)
        (mul_nonneg (le_of_lt hnpos) (le_of_lt hn1pos))
    simpa [mTailUP, hp] using hnonneg

/-- Casting the shifted index `n + (N + 1)` into the reals. -/
private lemma nat_cast_add3 (n N : ℕ) :
    ((n + (N + 1) : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) + 1 := by
  push_cast
  ring

/-- `mTailUP` is summable, by comparison with `2/n^2`. -/
private lemma summable_mTailUP : Summable mTailUP := by
  have hneg_le : ∀ n : ℕ, -mTailUP n ≤ 2 / (n : ℝ) ^ 2 := by
    intro n
    by_cases hn : Nat.Prime n
    · simpa [mTailUP, hn] using
        (neg_le_abs (mTailU n)).trans ((mTailU_abs_le hn).trans (inv_mul_pred_le_two_div_sq hn))
    · have hnonneg : (0 : ℝ) ≤ 2 / (n : ℝ) ^ 2 :=
        div_nonneg (by norm_num) (sq_nonneg _)
      simpa [mTailUP, hn] using hnonneg
  have hc : Summable fun n : ℕ => 2 / (n : ℝ) ^ 2 := by
    have h1 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (h1.mul_left 2).congr fun n => by rw [mul_one_div]
  exact (Summable.of_nonneg_of_le (fun n => neg_nonneg.mpr (mTailUP_nonpos n))
    hneg_le hc).neg.congr fun n => by simp

/-- The telescoping series `sum_n 1/((n+N)(n+N+1))` sums to `1/N`. -/
private lemma hasSum_telescoping (N : ℕ) (hN : 0 < N) :
    HasSum (fun n : ℕ =>
        (1 : ℝ) / (((n : ℝ) + (N : ℝ)) * ((n : ℝ) + (N : ℝ) + 1)))
      (1 / (N : ℝ)) := by
  let c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + (N : ℝ))
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc_succ : ∀ n : ℕ, c (n + 1) = 1 / ((n : ℝ) + (N : ℝ) + 1) := by
    intro n
    simp only [c]
    push_cast
    ring_nf
  have hterm : ∀ n : ℕ,
      (1 : ℝ) / (((n : ℝ) + (N : ℝ)) * ((n : ℝ) + (N : ℝ) + 1)) =
        c n - c (n + 1) := by
    intro n
    rw [hc_succ n]
    simp only [c]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have h1 : (0 : ℝ) < (n : ℝ) + (N : ℝ) := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) + (N : ℝ) + 1 := by linarith
    have h3 : ((n : ℝ) + (N : ℝ)) * ((n : ℝ) + (N : ℝ) + 1) ≠ 0 :=
      mul_ne_zero (ne_of_gt h1) (ne_of_gt h2)
    field_simp [ne_of_gt h1, ne_of_gt h2, h3]
    ring
  have hnonneg : ∀ n : ℕ, 0 ≤ c n - c (n + 1) := by
    intro n
    rw [hc_succ n]
    simp only [c]
    rw [sub_nonneg]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have h1 : (0 : ℝ) < (n : ℝ) + (N : ℝ) := by linarith
    have h2 : (n : ℝ) + (N : ℝ) ≤ (n : ℝ) + (N : ℝ) + 1 := by linarith
    exact one_div_le_one_div_of_le h1 h2
  have hfun : (fun n : ℕ =>
        (1 : ℝ) / (((n : ℝ) + (N : ℝ)) * ((n : ℝ) + (N : ℝ) + 1))) =
      (fun n : ℕ => c n - c (n + 1)) := by
    funext n
    exact hterm n
  rw [hfun]
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpartial : ∀ M : ℕ, (∑ i ∈ Finset.range M, (c i - c (i + 1))) = c 0 - c M := by
    intro M
    simpa using Finset.sum_range_sub' c M
  have htop : Tendsto (fun M : ℕ => (M : ℝ) + (N : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall (fun M : ℕ => by
      have hNn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      linarith)
  have hc0lim : Tendsto c atTop (nhds (0 : ℝ)) := by
    simpa [c, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp htop
  have hlim : Tendsto (fun M : ℕ => c 0 - c M) atTop (nhds (c 0 - 0)) :=
    tendsto_const_nhds.sub hc0lim
  have hc0 : c 0 = 1 / (N : ℝ) := by simp [c]
  simpa [hpartial, hc0] using hlim

theorem solution (x : ℝ) (hx : 1 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        1 / (⌊x⌋₊ : ℝ) := by
  let N : ℕ := ⌊x⌋₊
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.le_floor (by simpa using hx)
  have hNpos : 0 < N := by omega
  -- (i) `T(x)` as a sum over `range (N+1)` of the zero-extended summand.
  have hsumP : (∑ p ∈ Nat.primesLE N, mTailU p) =
      ∑ n ∈ Finset.range (N + 1), mTailUP n := by
    have hset : Nat.primesLE N = (Finset.range (N + 1)).filter Nat.Prime := by
      ext n
      simp [Nat.mem_primesLE]
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [mTailUP, Set.indicator]
  -- (ii) the full series is the `tsum` of the zero-extended summand.
  have htsub : (∑' p : Nat.Primes, mTailU (p : ℕ)) = ∑' n : ℕ, mTailUP n :=
    tsum_subtype {n : ℕ | Nat.Prime n} mTailU
  -- (iii) split the series at `N+1`.
  have hsplit : (∑ n ∈ Finset.range (N + 1), mTailUP n) +
        (∑' n : ℕ, mTailUP (n + (N + 1))) = ∑' n : ℕ, mTailUP n :=
    summable_mTailUP.sum_add_tsum_nat_add (N + 1)
  -- (iv) bound the tail by the telescoping sum, which equals `1/N`.
  let d : ℕ → ℝ := fun n =>
    (1 : ℝ) / (((n : ℝ) + (N : ℝ)) * ((n : ℝ) + (N : ℝ) + 1))
  have hd_summable : Summable d := (hasSum_telescoping N hNpos).summable
  have hcmp : ∀ n : ℕ, -mTailUP (n + (N + 1)) ≤ d n := by
    intro n
    have hn2 : 2 ≤ n + (N + 1) := by omega
    have hcast1 : ((n + (N + 1) : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) + 1 := nat_cast_add3 n N
    have hcast2 : (((n + (N + 1) : ℕ) : ℝ) - 1) = (n : ℝ) + (N : ℝ) := by
      rw [hcast1]
      ring
    calc
      -mTailUP (n + (N + 1))
          ≤ 1 / ((((n + (N + 1) : ℕ) : ℝ)) * ((((n + (N + 1) : ℕ) : ℝ) - 1))) :=
            neg_mTailUP_le (n + (N + 1)) hn2
      _ = 1 / (((n : ℝ) + (N : ℝ) + 1) * ((n : ℝ) + (N : ℝ))) := by
            rw [hcast2, hcast1]
      _ = d n := by
            simp only [d]
            ring_nf
  have hf_summ : Summable (fun n : ℕ => -mTailUP (n + (N + 1))) :=
    Summable.of_nonneg_of_le (fun n => neg_nonneg.mpr (mTailUP_nonpos _)) hcmp hd_summable
  have htail_le : (∑' n : ℕ, -mTailUP (n + (N + 1))) ≤ 1 / (N : ℝ) := by
    have h := hf_summ.tsum_le_tsum hcmp hd_summable
    have hd_tsum : (∑' n : ℕ, d n) = 1 / (N : ℝ) := (hasSum_telescoping N hNpos).tsum_eq
    simpa [hd_tsum] using h
  -- (v) `tsum` of the negated tail is minus the tail, so `sum <= tsum + 1/N`.
  have hTail_eq : (∑' n : ℕ, mTailUP (n + (N + 1))) =
      -(∑' n : ℕ, -mTailUP (n + (N + 1))) := by
    simpa using (tsum_neg (f := fun n : ℕ => -mTailUP (n + (N + 1))))
  have hdiff : (∑ n ∈ Finset.range (N + 1), mTailUP n) =
      (∑' n : ℕ, mTailUP n) - (∑' n : ℕ, mTailUP (n + (N + 1))) := by
    linarith
  have hfinal : (∑ n ∈ Finset.range (N + 1), mTailUP n) ≤
      (∑' n : ℕ, mTailUP n) + 1 / (N : ℝ) := by
    rw [hdiff]
    linarith
  -- (vi) translate back.
  calc
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
        = ∑ p ∈ Nat.primesLE N, mTailU p := by simp [mTailU, N]
    _ = ∑ n ∈ Finset.range (N + 1), mTailUP n := hsumP
    _ ≤ (∑' n : ℕ, mTailUP n) + 1 / (N : ℝ) := hfinal
    _ = (∑' p : Nat.Primes, mTailU (p : ℕ)) + 1 / (N : ℝ) := by rw [← htsub]
    _ = (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
          1 / (⌊x⌋₊ : ℝ) := by simp [mTailU, N]

end
