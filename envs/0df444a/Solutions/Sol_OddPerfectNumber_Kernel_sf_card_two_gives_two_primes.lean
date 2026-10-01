-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sf_card_two_gives_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T22:04:19.885953+00:00
-- url     : https://prove2.me/submissions/7e0ba589-356f-4006-bf33-59093ad31913

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- A square-free natural with exactly two distinct prime factors is a product of
-- two distinct primes `q < r`.
--
-- The API notes from the earlier repair of this same argument are preserved,
-- because each of them cost a remote round trip:
--
-- * `Nat.prod_primeFactors_of_squarefree` takes *only* the `Squarefree` proof;
--   `d` is implicit.  The resulting equation has `d` on the *right*.
-- * `Finset.card_eq_two` presents the set as `{x, y}` with `x` at the singleton
--   position, so membership is `Finset.mem_singleton_self x` and
--   `Finset.mem_insert_of_mem`; `Finset.mem_insert_self` instead wants a
--   `Finset` as its second argument.
-- * `simp` cannot reduce `∏ p ∈ ({x, y} : Finset ℕ), p` unaided, so the product
--   is rewritten by hand with `Finset.prod_pair`.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace SfCardTwoShape

theorem solution_aux {d : Nat} (hd0 : 0 < d) (hdsf : Squarefree d)
    (hcard : d.primeFactors.card = 2) :
    exists q r : Nat, q < r /\ q.Prime /\ r.Prime /\ d = q * r := by
  classical
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard
  have hxmem : x ∈ d.primeFactors := by
    rw [hset]
    exact Finset.mem_insert_self x {y}
  have hymem : y ∈ d.primeFactors := by
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hxprime : x.Prime := Nat.prime_of_mem_primeFactors hxmem
  have hyprime : y.Prime := Nat.prime_of_mem_primeFactors hymem
  have hprod : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdsf
  have hval : x * y = d := by
    have htwo : (∏ p ∈ ({x, y} : Finset ℕ), p) = x * y := by
      rw [Finset.prod_insert (by simpa using hxy)]
      simp
    rw [← hprod, hset]
    exact htwo.symm
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact ⟨x, y, hlt, hxprime, hyprime, hval.symm⟩
  · exact absurd heq hxy
  · exact ⟨y, x, hgt, hyprime, hxprime, by rw [Nat.mul_comm] at hval; exact hval.symm⟩

end SfCardTwoShape
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {d : Nat} (hd0 : 0 < d) (hdsf : Squarefree d)
    (hcard : d.primeFactors.card = 2) :
    exists q r : Nat, q < r /\ q.Prime /\ r.Prime /\ d = q * r :=
  OddPerfectNumber.Kernel.SfCardTwoShape.solution_aux hd0 hdsf hcard
