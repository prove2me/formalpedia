-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_lower_bound_small
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-27T14:32:55.177584+00:00
-- url     : https://prove2.me/submissions/81e02074-f436-4b7e-9b17-7eeb4cf35ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
`TaoFivePrimes.mawia_reciprocal_sum_lower_bound_small`

Target (Mawia 2017, lower half, finite range 2 <= x <= 10^8):

    log log x + (gamma + sum_p (log (1 - 1/p) + 1/p)) - 4/(log x)^3
        <= sum_{p <= floor x} 1/p .

Write

    P(x) = prod_{p <= floor x} p/(p-1),
    T(x) = sum_{p <= floor x} (log (1 - 1/p) + 1/p),
    T(inf) = sum'_p (log (1 - 1/p) + 1/p),
    B = gamma + T(inf)   (the Meissel--Mertens constant).

Term by term, for a prime p,

    log (p/(p-1)) + (log (1 - 1/p) + 1/p) = -log (1 - 1/p) + log (1 - 1/p) + 1/p = 1/p,

because p/(p-1) = (1 - 1/p)^{-1}. Summing over p <= floor x and using
`Real.log_prod` gives the exact identity

    sum_{p <= x} 1/p = log P(x) + T(x).                                    (1)

Two inputs, both external:

  * `rosser_schoenfeld_product_bound_lower` (this file's new citation child):
        e^gamma log x < P(x)      for 2 <= x <= 10^8.
    Taking logarithms (log x > 0 because x >= 2),
        gamma + log log x < log P(x).                                      (2)
  * `mertens_tail_le_partial_sum` (Proved on the platform):
        T(inf) <= T(x).                                                    (3)

Adding (2) and (3) and using (1),

    log log x + gamma + T(inf) < log P(x) + T(x) = sum_{p <= x} 1/p ,

and since 4/(log x)^3 >= 0 for x >= 2 the target's left-hand side is at most
log log x + B, which proves the claim.

Remarks on scope.

  * The whole content is the identity (1) plus two quotations; no numerical
    value of the Meissel--Mertens constant is needed, and no series tail is
    estimated. This is why the lower half is so much cheaper than the upper
    half: there the tail T(x) - T(inf) must be bounded *above*, while here the
    proved inequality T(inf) <= T(x) is exactly the direction wanted.
  * The lower product bound is only valid to 10^8, and genuinely fails beyond:
    Diamond--Pintz (2009) showed sqrt(x) (P(x) - e^gamma log x) is unbounded
    above and below. So this reduction does NOT apply to the sibling node
    `mawia_reciprocal_sum_lower_bound_large` (x >= 10^8).
-/
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_lower
import Theorems.Thm_TaoFivePrimes_mertens_tail_le_partial_sum
import Mathlib

open BigOperators

noncomputable section

/-- Term identity `log (p/(p-1)) + (log (1 - 1/p) + 1/p) = 1/p` for primes `p`. -/
private lemma mawia_term_identity {p : ℕ} (hp : Nat.Prime p) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) +
        (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) = 1 / (p : ℝ) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpm1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hfrac : (p : ℝ) / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by
    field_simp [hp_ne, hpm1_ne]
  rw [hfrac, Real.log_inv]
  ring

/-- `log (prod_{p in s} p/(p-1)) = sum_{p in s} log (p/(p-1))`, valid because
every factor is a nonzero real for prime `p`. -/
private lemma log_mertens_product (n : ℕ) :
    Real.log (∏ p ∈ Nat.primesLE n, (p : ℝ) / ((p : ℝ) - 1)) =
      ∑ p ∈ Nat.primesLE n, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
  apply Real.log_prod
  intro p hp
  have hpprime : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
  have hpm1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  exact div_ne_zero hp_ne hpm1_ne

/-- The exact splitting (1): `sum 1/p = log P + T`. -/
private lemma reciprocal_sum_split (n : ℕ) :
    (∑ p ∈ Nat.primesLE n, 1 / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE n, Real.log ((p : ℝ) / ((p : ℝ) - 1))) +
        (∑ p ∈ Nat.primesLE n, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by
  calc
    (∑ p ∈ Nat.primesLE n, 1 / (p : ℝ))
        = ∑ p ∈ Nat.primesLE n,
            (Real.log ((p : ℝ) / ((p : ℝ) - 1)) +
              (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact (mawia_term_identity (Nat.mem_primesLE.mp hp).2).symm
    _ = (∑ p ∈ Nat.primesLE n, Real.log ((p : ℝ) / ((p : ℝ) - 1))) +
          (∑ p ∈ Nat.primesLE n, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by
            simp [Finset.sum_add_distrib]

theorem solution (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
        4 / (Real.log x) ^ 3 ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
  -- log x > 0 (x >= 2 > 1), so both the logarithm and 4/(log x)^3 behave.
  have hx_gt_one : (1 : ℝ) < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  -- (2): the quoted lower product bound, in logarithmic form.
  have hprod :=
    TaoFivePrimes.rosser_schoenfeld_product_bound_lower x hx hsmall
  have hlog_left :
      Real.log (Real.exp Real.eulerMascheroniConstant * Real.log x) =
        Real.eulerMascheroniConstant + Real.log (Real.log x) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)) hlogx_ne,
      Real.log_exp]
  have hlog_prod :
      Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) :=
    log_mertens_product ⌊x⌋₊
  have hmain :
      Real.log (Real.log x) + Real.eulerMascheroniConstant <
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := by
    calc
      Real.log (Real.log x) + Real.eulerMascheroniConstant
          = Real.log (Real.exp Real.eulerMascheroniConstant * Real.log x) := by
              linarith [hlog_left]
      _ < Real.log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)) :=
              Real.log_lt_log
                (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hlogx_pos) hprod
      _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) := hlog_prod
  -- (3): the already-proved Mertens tail domination.
  have htail := TaoFivePrimes.mertens_tail_le_partial_sum x
  -- add them and use the splitting (1)
  have hstrict :
      Real.log (Real.log x) +
          (Real.eulerMascheroniConstant +
            ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) <
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
    calc
      Real.log (Real.log x) +
          (Real.eulerMascheroniConstant +
            ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
          = (Real.log (Real.log x) + Real.eulerMascheroniConstant) +
              (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by ring
      _ < (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1))) +
            (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) :=
              add_lt_add_of_lt_of_le hmain htail
      _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := (reciprocal_sum_split ⌊x⌋₊).symm
  -- 4/(log x)^3 >= 0, so the extra subtracted term only weakens the claim.
  have hpow_pos : 0 < (Real.log x) ^ 3 := pow_pos hlogx_pos 3
  have hnonneg : 0 ≤ 4 / (Real.log x) ^ 3 := div_nonneg (by norm_num) (le_of_lt hpow_pos)
  linarith
