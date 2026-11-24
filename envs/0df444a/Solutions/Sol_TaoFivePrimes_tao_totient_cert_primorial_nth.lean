-- Prove2me | solution 1 for TaoFivePrimes.tao_totient_cert_primorial_nth
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T20:46:40.438092+00:00
-- url     : https://prove2.me/submissions/3130cf6f-c10b-4476-b797-26638e17029c

import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
open Finset

set_option maxHeartbeats 1000000

namespace TaoFivePrimes

/-- The primorial of the `(k+1)`-st prime is the product of the first `k+1` primes. -/
theorem solution (k : ℕ) :
    primorial (Nat.nth Nat.Prime k) = ∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro n
    obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (n+1)
    exact ⟨p, hpp, by omega⟩
  rw [primorial_eq_prod_primesLE]
  have himg : Nat.primesLE (Nat.nth Nat.Prime k) = (Finset.range (k+1)).image (Nat.nth Nat.Prime) := by
    ext p
    rw [Nat.mem_primesLE, Finset.mem_image]
    constructor
    · rintro ⟨hpk, hpp⟩
      have hc : Nat.count Nat.Prime p ≤ k := by
        by_contra h
        have hlt : k < Nat.count Nat.Prime p := by omega
        have := Nat.nth_lt_of_lt_count (p := Nat.Prime) hlt
        omega
      exact ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr (by omega), Nat.nth_count hpp⟩
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_range] at hi
      exact ⟨(Nat.nth_le_nth hinf).mpr (by omega), Nat.nth_mem_of_infinite hinf i⟩
  rw [himg, Finset.prod_image (fun x _ y _ hxy => Nat.nth_injective hinf hxy)]

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (k : ℕ) :
    primorial (Nat.nth Nat.Prime k) = ∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i :=
  TaoFivePrimes.solution k

#print axioms solution
