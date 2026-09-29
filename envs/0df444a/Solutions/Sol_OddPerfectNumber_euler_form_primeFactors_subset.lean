-- Prove2me | solution 1 for OddPerfectNumber.euler_form_primeFactors_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:05:18.576737+00:00
-- url     : https://prove2.me/submissions/10bea032-7fb5-481e-890b-c079d0b71d18

import Mathlib

-- STAGED, NOT YET SUBMITTED (awaits publish job ab021592).
-- Element-chase proof using only accepted-use lemma shapes
-- (`Nat.mem_primeFactors` triple, `Nat.Prime.dvd_mul`,
-- `dvd_of_dvd_pow`, `Nat.prime_dvd_prime_iff_eq`).
theorem solution (p k m : Nat) (hp : p.Prime)
    (hm : m ≠ 0) :
    (p ^ k * m ^ 2).primeFactors ⊆ {p} ∪ m.primeFactors := by
  intro x hx
  obtain ⟨hxp, hxdvd, -⟩ := Nat.mem_primeFactors.mp hx
  simp only [Finset.mem_union]
  rcases (Nat.Prime.dvd_mul hxp).mp hxdvd with h1 | h2
  · exact Or.inl (Finset.mem_singleton.mpr
      ((Nat.prime_dvd_prime_iff_eq hxp hp).mp (hxp.dvd_of_dvd_pow h1)))
  · exact Or.inr (Nat.mem_primeFactors.mpr
      ⟨hxp, hxp.dvd_of_dvd_pow h2, hm⟩)
