-- Prove2me | solution 1 for TaoFivePrimes.mertens_tail_upper
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-27T15:38:41.060097+00:00
-- url     : https://prove2.me/submissions/1f96ff8c-9145-4be0-aec4-c638d3c9df81

/-
`TaoFivePrimes.mertens_tail_upper`

Write, for `N = floor x`,

    T(N)   = sum_{p <= N} (log (1 - 1/p) + 1/p),
    T(inf) = sum'_p       (log (1 - 1/p) + 1/p),

the finite and the infinite Mertens correction sums.  The platform already has
`mertens_tail_le_partial_sum`, i.e. `T(inf) <= T(N)`: it says the correction sum
*overshoots* its limit.  This node bounds the overshoot from above:

    T(N) - T(inf) <= 1/N          for x >= 2 (so N >= 2).

Both halves are needed because the Mawia reciprocal-sum bounds go through the
exact identity `sum_{p <= x} 1/p = log P(x) + T(N)` with
`P(x) = prod_{p <= x} p/(p-1)`: the *lower* half needs `T(N) - T(inf) >= 0`
(the proved node), the *upper* half needs `T(N) - T(inf) <= 1/N` (this node).
That asymmetry is why the lower half costs two quotations and the upper half
costs a real estimate.

**The estimate, and where the constant comes from.**  Put `u = 1/p`.  For
`0 <= u < 1` the two standard logarithm inequalities

    1 - (1-u)^(-1) <= log (1-u)   (Real.one_sub_inv_le_log_of_pos),
    log (1-u)      <= (1-u) - 1    (Real.log_le_sub_one_of_pos)

give, on the one hand, `log (1-u) + u <= 0`, i.e. every correction term is
nonpositive (so the partial sums decrease to the limit), and on the other

    0 <= -(log (1-u) + u) <= -1 + (1-u)^(-1) - u = u^2/(1-u) = 1/(p (p-1)).

Since `1/(p(p-1)) = 1/(p-1) - 1/p` telescopes, the tail over *all* integers
above `N` sums to exactly `1/N`, and the prime-supported tail is dominated by
it:

    T(N) - T(inf) = sum_{p > N} -(log (1-1/p) + 1/p)
                 <= sum_{n > N} (1/(n-1) - 1/n) = 1/N.

No prime number theorem is used -- the crudest possible step, replacing a sum
over primes by a sum over all integers, is what produces the constant 1.

**Remark on the constant (not claimed here).**  The sharp constant is `1/(2N)`.
It comes from the second-order estimate `|log (1-u) + u| <= u^2/(2(1-u))`,
which after `x = 1/(1-u)` is the classical `log x <= (x - 1/x)/2` for `x >= 1`
(the derivative of the difference is `(x-1)^2/(2x^2) >= 0`), giving
`T(N) - T(inf) <= sum_{p>N} 1/(2 p (p-1)) <= 1/(2N)`.  Its Lean proof needs a
monotonicity argument, so this node states the weaker, derivative-free `1/N`.

**Infinite sums.**  `Real.tsum_le_of_sum_range_le` bounds a `tsum` of a
nonnegative sequence by a uniform bound on its finite partial sums, so no
separate summability proof of the prime series is needed for the bound; the
splitting of `sum'_n` into the head `n < N+1` and the tail uses
`Summable.sum_add_tsum_nat_add`, with summability obtained from
`summable_of_sum_range_le` applied to the *shifted* sequence.  `tsum_subtype`
moves `sum' p : Nat.Primes` to a sum over `Nat` with a prime indicator.
-/
import Mathlib

open BigOperators

noncomputable section


/-- The Mertens correction term at `n`. -/
private def mtuTerm (n : ℕ) : ℝ := Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)

/-- Its negative; nonnegative for `n >= 2`. -/
private def mtuGap (n : ℕ) : ℝ := -(mtuTerm n)

/-- The gap, restricted to primes and extended by `0` off the primes. -/
private def mtuGapP (n : ℕ) : ℝ := if Nat.Prime n then mtuGap n else 0

/-- The telescoping majorant: `1/((n+1) n)` at `n = j + N`. -/
private def mtuTele (N j : ℕ) : ℝ :=
  (1 : ℝ) / (((j + N + 1 : ℕ) : ℝ) * ((j + N : ℕ) : ℝ))

/-- Every correction term is nonpositive, i.e. the gap is nonnegative. -/
private lemma mtuGap_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ mtuGap n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_one : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hu_lt : (1 : ℝ) / (n : ℝ) < 1 := by
    calc
      (1 : ℝ) / (n : ℝ) < (n : ℝ) / (n : ℝ) := div_lt_div_of_pos_right hn_one hn_pos
      _ = 1 := by field_simp [ne_of_gt hn_pos]
  have hpos : 0 < 1 - 1 / (n : ℝ) := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  dsimp [mtuGap, mtuTerm]
  linarith

/-- The gap at `n >= 2` is at most `1/(n (n-1))`. -/
private lemma mtuGap_le {n : ℕ} (hn : 2 ≤ n) :
    mtuGap n ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_one : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hu_lt : (1 : ℝ) / (n : ℝ) < 1 := by
    calc
      (1 : ℝ) / (n : ℝ) < (n : ℝ) / (n : ℝ) := div_lt_div_of_pos_right hn_one hn_pos
      _ = 1 := by field_simp [ne_of_gt hn_pos]
  have hpos : 0 < 1 - 1 / (n : ℝ) := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hneg : -Real.log (1 - 1 / (n : ℝ)) ≤ -1 + (1 - 1 / (n : ℝ))⁻¹ := by
    linarith
  have hident : -1 + (1 - 1 / (n : ℝ))⁻¹ - 1 / (n : ℝ) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hnm1_ne : (n : ℝ) - 1 ≠ 0 := by linarith
    have hone_ne : 1 - 1 / (n : ℝ) ≠ 0 := ne_of_gt hpos
    field_simp [hn_ne, hnm1_ne, hone_ne]
    ring
  dsimp [mtuGap, mtuTerm]
  linarith

/-- The prime-restricted gap is nonnegative everywhere. -/
private lemma mtuGapP_nonneg (n : ℕ) : 0 ≤ mtuGapP n := by
  by_cases hp : Nat.Prime n
  · simpa [mtuGapP, hp] using mtuGap_nonneg (n := n) hp.two_le
  · simp [mtuGapP, hp]

/-- The prime-restricted gap is dominated by the telescoping majorant. -/
private lemma mtuGapP_le {n : ℕ} (hn : 2 ≤ n) :
    mtuGapP n ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  by_cases hp : Nat.Prime n
  · simpa [mtuGapP, hp] using mtuGap_le (n := n) hn
  · rw [mtuGapP, if_neg hp]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
    have hn_one : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
    have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
      mul_pos hn_pos (sub_pos.mpr hn_one)
    exact div_nonneg zero_le_one (le_of_lt hden_pos)

/-- The majorant term is a telescoping difference. -/
private lemma mtuTele_eq (N j : ℕ) (hN : 0 < N) :
    mtuTele N j =
      (1 : ℝ) / ((j : ℝ) + (N : ℝ)) - (1 : ℝ) / (((j + 1 : ℕ) : ℝ) + (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
  have ha_pos : 0 < (j : ℝ) + (N : ℝ) := by linarith
  have ha_ne : (j : ℝ) + (N : ℝ) ≠ 0 := ne_of_gt ha_pos
  have h1 : (((j + N + 1 : ℕ) : ℝ)) = (((j + 1 : ℕ) : ℝ) + (N : ℝ)) := by
    exact_mod_cast (by omega : j + N + 1 = (j + 1) + N)
  have h0 : (((j + N : ℕ) : ℝ)) = (j : ℝ) + (N : ℝ) := by norm_num
  have hsucc : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by norm_num
  rw [mtuTele, h1, h0, hsucc]
  have hb_pos : 0 < (j : ℝ) + 1 + (N : ℝ) := by linarith
  have hb_ne : (j : ℝ) + 1 + (N : ℝ) ≠ 0 := ne_of_gt hb_pos
  have hab_ne : ((j : ℝ) + 1 + (N : ℝ)) * ((j : ℝ) + (N : ℝ)) ≠ 0 :=
    mul_ne_zero hb_ne ha_ne
  field_simp [ha_ne, hb_ne, hab_ne]
  ring

/-- Partial sums of the majorant telescope to `1/N - 1/(K+N)`. -/
private lemma mtuTele_sum (N K : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range K, mtuTele N j) =
      1 / (N : ℝ) - 1 / ((K : ℝ) + (N : ℝ)) := by
  have h := Finset.sum_range_sub' (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + (N : ℝ))) K
  calc
    (∑ j ∈ Finset.range K, mtuTele N j)
        = ∑ j ∈ Finset.range K,
            ((1 : ℝ) / ((j : ℝ) + (N : ℝ)) -
              (1 : ℝ) / (((j + 1 : ℕ) : ℝ) + (N : ℝ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact mtuTele_eq N j hN
    _ = (1 : ℝ) / ((0 : ℕ) + (N : ℝ) : ℝ) - (1 : ℝ) / ((K : ℝ) + (N : ℝ)) := by
            simpa using h
    _ = 1 / (N : ℝ) - 1 / ((K : ℝ) + (N : ℝ)) := by norm_num

/-- The shifted prime-gap series has partial sums bounded by `1/N`. -/
private lemma mtuGapP_tail_partial (N : ℕ) (hN : 0 < N) (K : ℕ) :
    (∑ j ∈ Finset.range K, mtuGapP (j + N + 1)) ≤ 1 / (N : ℝ) := by
  calc
    (∑ j ∈ Finset.range K, mtuGapP (j + N + 1))
        ≤ ∑ j ∈ Finset.range K, mtuTele N j := by
            apply Finset.sum_le_sum
            intro j hj
            have h2 : 2 ≤ j + N + 1 := by omega
            have hle := mtuGapP_le (n := j + N + 1) h2
            have hsub : (((j + N + 1 : ℕ) : ℝ) - 1) = ((j + N : ℕ) : ℝ) := by
              norm_num
            simpa [mtuTele, hsub] using hle
    _ = 1 / (N : ℝ) - 1 / ((K : ℝ) + (N : ℝ)) := mtuTele_sum N K hN
    _ ≤ 1 / (N : ℝ) := by
            have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
            have hKnn : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
            have hnonneg : 0 ≤ (1 : ℝ) / ((K : ℝ) + (N : ℝ)) := by
              exact div_nonneg zero_le_one (le_of_lt (by linarith))
            linarith

/-- The whole shifted prime-gap series sums to at most `1/N`. -/
private lemma mtuGapP_tail_tsum (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, mtuGapP (j + N + 1)) ≤ 1 / (N : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact mtuGapP_nonneg (j + N + 1)
  · intro K
    exact mtuGapP_tail_partial N hN K

/-- `sum' p : Nat.Primes` of the gap equals `sum'_n` of the prime indicator. -/
private lemma mtuGap_tsum_eq :
    (∑' p : Nat.Primes, mtuGap (p : ℕ)) = ∑' n : ℕ, mtuGapP n := by
  change (∑' p : {n : ℕ // Nat.Prime n}, mtuGap (p : ℕ)) = ∑' n : ℕ, mtuGapP n
  calc
    (∑' p : {n : ℕ // Nat.Prime n}, mtuGap (p : ℕ))
        = ∑' n : ℕ, ({n : ℕ | Nat.Prime n}).indicator (fun n : ℕ => mtuGap n) n :=
            tsum_subtype (s := {n : ℕ | Nat.Prime n}) (f := fun n : ℕ => mtuGap n)
    _ = ∑' n : ℕ, mtuGapP n := by
            congr with n
            simp [mtuGapP, Set.indicator]

/-- The head `n < N+1` of the indicator series is the sum over primes `<= N`. -/
private lemma mtuGapP_head (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), mtuGapP n) = ∑ p ∈ Nat.primesLE N, mtuGap p := by
  simp [Nat.primesLE, Nat.primesBelow, mtuGapP, Finset.sum_filter]

/-- The gap series is dominated by its head plus `1/N`. -/
private lemma mtuGapP_tsum_le (N : ℕ) (hN : 0 < N) :
    (∑' n : ℕ, mtuGapP n) ≤ (∑ p ∈ Nat.primesLE N, mtuGap p) + 1 / (N : ℝ) := by
  have hsumm_shift : Summable (fun j : ℕ => mtuGapP (j + (N + 1))) :=
    summable_of_sum_range_le (fun j => mtuGapP_nonneg (j + (N + 1)))
      (fun K => mtuGapP_tail_partial N hN K)
  have hsumm : Summable mtuGapP := (summable_nat_add_iff (N + 1)).1 hsumm_shift
  have hsplit := hsumm.sum_add_tsum_nat_add (N + 1)
  calc
    (∑' n : ℕ, mtuGapP n)
        = (∑ j ∈ Finset.range (N + 1), mtuGapP j) +
            (∑' j : ℕ, mtuGapP (j + (N + 1))) := hsplit.symm
    _ ≤ (∑ p ∈ Nat.primesLE N, mtuGap p) + 1 / (N : ℝ) := by
          have htail := mtuGapP_tail_tsum N hN
          rw [mtuGapP_head N]
          exact add_le_add (le_refl (∑ p ∈ Nat.primesLE N, mtuGap p)) htail

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        1 / (⌊x⌋₊ : ℝ) := by
  let N : ℕ := ⌊x⌋₊
  have hN_two : 2 ≤ N := by
    exact Nat.le_floor hx
  have hN_pos : 0 < N := by omega
  have hgap := mtuGapP_tsum_le N hN_pos
  have hgap' : (∑' p : Nat.Primes, mtuGap (p : ℕ)) ≤
      (∑ p ∈ Nat.primesLE N, mtuGap p) + 1 / (N : ℝ) := by
    simpa [mtuGap_tsum_eq] using hgap
  -- negate: pass from the gap `-(term)` back to the correction term itself
  have hterm_tsum :
      (∑' p : Nat.Primes, mtuTerm (p : ℕ)) =
        - (∑' p : Nat.Primes, mtuGap (p : ℕ)) := by
    rw [← tsum_neg]
    simp [mtuGap]
  have hfin_term :
      (∑ p ∈ Nat.primesLE N, mtuTerm p) = - (∑ p ∈ Nat.primesLE N, mtuGap p) := by
    simp [mtuGap]
  calc
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
        = ∑ p ∈ Nat.primesLE N, mtuTerm p := by simp [mtuTerm, N]
    _ = - (∑ p ∈ Nat.primesLE N, mtuGap p) := hfin_term
    _ ≤ -(∑' p : Nat.Primes, mtuGap (p : ℕ)) + 1 / (N : ℝ) := by linarith
    _ = (∑' p : Nat.Primes, mtuTerm (p : ℕ)) + 1 / (N : ℝ) := by rw [hterm_tsum]
    _ = (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
          1 / (⌊x⌋₊ : ℝ) := by simp [mtuTerm, N]


end
