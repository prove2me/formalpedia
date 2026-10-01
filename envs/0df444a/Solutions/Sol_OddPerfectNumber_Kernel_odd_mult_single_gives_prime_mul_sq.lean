-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_mult_single_gives_prime_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:46:19.882283+00:00
-- url     : https://prove2.me/submissions/16e4d68d-c951-4203-bf4b-e796f22a3a5b

import Mathlib
 theorem odd_single_prop {a t : ℕ} (ha0:a ≠ 0) (ht:t.Prime)
    (ht0:¬ Even (a.factorization t)) (hall:∀ z:ℕ,z ≠ t → Even (a.factorization z)) :
    ∃ y:ℕ,a=t*y^2 := by
  refine ⟨Nat.floorRoot 2 a,?_⟩
  have hy:Nat.floorRoot 2 a ≠ 0:=Nat.floorRoot_ne_zero.mpr ⟨by norm_num,ha0⟩
  apply Nat.eq_of_factorization_eq ha0 (mul_ne_zero ht.ne_zero (pow_ne_zero _ hy))
  intro q
  rw [Nat.factorization_mul ht.ne_zero (pow_ne_zero _ hy),ht.factorization,Nat.factorization_pow,Nat.factorization_floorRoot]
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.floorDiv_def,Finsupp.mapRange_apply,Nat.floorDiv_eq_div]
  by_cases hq:q=t
  · subst q
    simp only [Finsupp.single_eq_same]
    have hodd:=Nat.not_even_iff_odd.mp ht0
    obtain ⟨k,hk⟩:=hodd
    omega
  · simp only [Finsupp.single_eq_of_ne hq]
    obtain ⟨k,hk⟩:=hall q hq
    omega

theorem solution {a t : Nat} (ha0 : a != 0) (ht : t.Prime)
    (ht0 : ! Even (a.factorization t))
    (hall : forall z : Nat, z != t -> Even (a.factorization z)) :
    exists y : Nat, a = t * y ^ 2 := by
  apply odd_single_prop (by simpa using ha0) ht (by simpa using ht0)
  intro z hz
  exact hall z (by simpa using hz)
