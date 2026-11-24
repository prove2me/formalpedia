-- Prove2me | solution 1 for RSBDDHard.identity_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:54:46.315276+00:00
-- url     : https://prove2.me/submissions/2badd1e7-1cfd-470a-883b-d35acd6b80bd

import Mathlib
import Definitions.Def_RSBDDHard_recipProd

set_option autoImplicit false

open RSBDDHard

private lemma coeff_step {R : Type*} [CommRing R] (a : R) (P : Polynomial R) :
    ((1 - Polynomial.C a * Polynomial.X) * P).coeff 0 = P.coeff 0 ∧
    ((1 - Polynomial.C a * Polynomial.X) * P).coeff 1 = P.coeff 1 - a * P.coeff 0 ∧
    ((1 - Polynomial.C a * Polynomial.X) * P).coeff 2 = P.coeff 2 - a * P.coeff 1 := by
  have e : (1 - Polynomial.C a * Polynomial.X) * P
      = P - Polynomial.C a * (Polynomial.X * P) := by ring
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
  · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

private lemma invariant {R : Type*} [CommRing R] (S : Finset R) :
    (recipProd S).coeff 0 = 1 ∧ powerSum S 1 = -(recipProd S).coeff 1 ∧
    powerSum S 2 = (recipProd S).coeff 1 ^ 2 - 2 * (recipProd S).coeff 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [recipProd, powerSum, Polynomial.coeff_one]
  | insert a S ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hP : recipProd (insert a S) = (1 - Polynomial.C a * Polynomial.X) * recipProd S := by
      simp [recipProd, Finset.prod_insert ha]
    have hp : ∀ j, powerSum (insert a S) j = a ^ j + powerSum S j := by
      intro j; simp [powerSum, Finset.sum_insert ha]
    obtain ⟨e0, e1, e2⟩ := coeff_step a (recipProd S)
    rw [hP, hp, hp, e0, e1, e2, h0]
    refine ⟨rfl, ?_, ?_⟩
    · rw [h1]; ring
    · rw [h2]; ring

theorem solution {R : Type*} [CommRing R] (S : Finset R) :
    powerSum S 1 = -(recipProd S).coeff 1 ∧
    powerSum S 2 = (recipProd S).coeff 1 ^ 2 - 2 * (recipProd S).coeff 2 :=
  (invariant S).2
