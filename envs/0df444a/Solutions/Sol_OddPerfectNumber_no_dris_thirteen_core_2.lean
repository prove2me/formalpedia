-- Prove2me | solution 2 for OddPerfectNumber.no_dris_thirteen_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:11:47.001144+00:00
-- url     : https://prove2.me/submissions/536e66c1-b4fa-4cd4-b792-a6607e9a41a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_witnessed_core

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  obtain ⟨q1, hq1mem, q2, hq2mem, hne⟩ := Finset.one_lt_card.1 hk1
  have h1 := Finset.mem_erase.1 hq1mem
  have h2 := Finset.mem_erase.1 hq2mem
  have hq1p : q1.Prime := Nat.prime_of_mem_primeFactors h1.2
  have hq2p : q2.Prime := Nat.prime_of_mem_primeFactors h2.2
  exact OddPerfectNumber.no_dris_thirteen_witnessed_core p k m s q1 q2 hp hp2 hp4 hk4 hk13
    hm hpm hs2 hs_not_even hne hq1p hq2p (hq1p.odd_of_ne_two h1.1) (hq2p.odd_of_ne_two h2.1)
    (Nat.dvd_of_mem_primeFactors h1.2) (Nat.dvd_of_mem_primeFactors h2.2) hs_dvd

#print axioms solution
