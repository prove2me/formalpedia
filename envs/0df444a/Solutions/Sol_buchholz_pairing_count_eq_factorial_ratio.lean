-- Prove2me | solution 1 for buchholz_pairing_count_eq_factorial_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T03:12:30.693328+00:00
-- url     : https://prove2.me/submissions/802f17fd-fcfd-4702-8558-b7ae90f81c73

import Theorems.Thm_buchholz_pairing_count_eq_two_cycle_type_card
import Theorems.Thm_two_cycle_type_card_eq_factorial_ratio

open MatrixCompletion

/-- Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 25.  The displayed
Buchholz constant `(2n)!/(2^n n!)` is the number of pair partitions of the
`2n` Rademacher factors.  This formal bridge identifies pair partitions with
the cycle type consisting of `n` two-cycles, then applies the cycle-type
cardinality formula. -/
theorem solution (n : Nat) :
    (Fintype.card (BuchholzPairing n) : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) := by
  have hCard :=
    congrArg (fun k : Nat => (k : ℝ))
      (buchholz_pairing_count_eq_two_cycle_type_card n)
  exact hCard.trans (two_cycle_type_card_eq_factorial_ratio n)
