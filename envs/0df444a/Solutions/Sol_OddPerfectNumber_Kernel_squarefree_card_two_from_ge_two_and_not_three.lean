-- Prove2me | solution 1 for OddPerfectNumber.Kernel.squarefree_card_two_from_ge_two_and_not_three
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T13:09:26.178152+00:00
-- url     : https://prove2.me/submissions/e471d7e0-9f5b-4474-9a5c-e5e9afbab9df

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- Phase F bridge.  A square-free number with at least two prime factors and
-- fewer than three is a product of two distinct primes.
--
-- The hypotheses pin the cardinality to exactly `2`; the ordered prime pair
-- then comes from the already-proved characterisation
-- `squarefree_card_two_eq_two_primes` (04aeb617).  This is the shape the k = 5
-- hard residual must exclude: once `2 ≤ d2.primeFactors.card` is known, a
-- failure of `3 ≤ d2.primeFactors.card` leaves exactly the two-prime kernel.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_squarefree_card_two_eq_two_primes

namespace OddPerfectNumber.Kernel
namespace CardExactlyTwo

theorem solution_aux {d : Nat} (hdsf : Squarefree d) (hge2 : 2 ≤ d.primeFactors.card)
    (hnge3 : ¬ 3 ≤ d.primeFactors.card) :
    ∃ q r : Nat, q < r ∧ q.Prime ∧ r.Prime ∧ d = q * r := by
  -- `2 ≤ card` and `¬ 3 ≤ card` leave `card = 2` as the only possibility.
  have hcard : d.primeFactors.card = 2 := by omega
  exact OddPerfectNumber.Kernel.squarefree_card_two_eq_two_primes hdsf hcard

end CardExactlyTwo
end OddPerfectNumber.Kernel

-- The target declares its binders inside `namespace OddPerfectNumber.Kernel`,
-- so the namespace must be opened for a top-level `theorem solution`.  The
-- single import above is a *Proved* child, so the namespace exists remotely.
open OddPerfectNumber.Kernel

theorem solution {d : Nat} (hdsf : Squarefree d) (hge2 : 2 ≤ d.primeFactors.card)
    (hnge3 : ¬ 3 ≤ d.primeFactors.card) :
    ∃ q r : Nat, q < r ∧ q.Prime ∧ r.Prime ∧ d = q * r :=
  OddPerfectNumber.Kernel.CardExactlyTwo.solution_aux hdsf hge2 hnge3
