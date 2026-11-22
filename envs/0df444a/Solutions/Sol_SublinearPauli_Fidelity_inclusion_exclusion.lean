-- Prove2me | solution 1 for SublinearPauli.Fidelity.inclusion_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T14:37:15.235648+00:00
-- url     : https://prove2.me/submissions/eaf4d6c7-7ee8-4ca2-96f5-f6e0b4c9276a

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli

open ClassicalShadow.Linear
open SublinearPauli.Fidelity
theorem solution {N : ℕ} (Q Q' : PauliString N) (h : Compatible Q Q') :
    ((weight Q : ℤ) + weight Q' - weight (union Q Q') =
      ∑ i, ((if Q i ≠ Letter.I then (1 : ℤ) else 0) + (if Q' i ≠ Letter.I then 1 else 0) -
        (if Q i ≠ Letter.I ∨ Q' i ≠ Letter.I then 1 else 0))) ∧
    (∑ i, ((if Q i ≠ Letter.I then (1 : ℤ) else 0) + (if Q' i ≠ Letter.I then 1 else 0) -
        (if Q i ≠ Letter.I ∨ Q' i ≠ Letter.I then 1 else 0)) =
      ∑ i, (if Q i = Q' i ∧ Q i ≠ Letter.I then (1 : ℤ) else 0)) ∧
    (∑ i, (if Q i = Q' i ∧ Q i ≠ Letter.I then (1 : ℤ) else 0) = weight (inter Q Q')) := by
  classical
  have hw (R : PauliString N) :
      (weight R : ℤ) = ∑ i, if R i ≠ Letter.I then (1 : ℤ) else 0 := by
    simp [weight, Finset.sum_ite]
  have hu (i : Fin N) : union Q Q' i ≠ Letter.I ↔ Q i ≠ Letter.I ∨ Q' i ≠ Letter.I := by
    simp only [union]
    split_ifs <;> simp_all
  have hi (i : Fin N) : inter Q Q' i ≠ Letter.I ↔ Q i = Q' i ∧ Q i ≠ Letter.I := by
    simp only [inter]
    split_ifs <;> simp_all
  constructor
  · rw [hw Q, hw Q', hw (union Q Q'), ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hu]
  constructor
  · apply Finset.sum_congr rfl
    intro i _
    rcases h i with he | he | he
    · rw [he]
      by_cases hz : Q' i = Letter.I <;> simp [hz]
    · simp [he]
    · simp [he]
  · rw [hw (inter Q Q')]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hi]

