-- Prove2me | solution 1 for TemperleyLieb.Gram.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:39:00.26464+00:00
-- url     : https://prove2.me/submissions/e6ccbe83-7db4-406f-b1bc-b463d570a25b

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_JM

open scoped BigOperators

namespace Aux_TLG34
open TemperleyLieb.Gram

lemma p_succ_succ (a : ℕ) : p (a + 2) = Polynomial.X * p (a + 1) - p a := rfl

lemma key : ∀ a b : ℕ, p (a + 1) * p (b + 1) - p a * p b = p (a + b + 1) := by
  intro a
  induction a with
  | zero =>
    intro b
    have h1 : p 1 = 1 := rfl
    have h0 : p 0 = 0 := rfl
    rw [h1, h0, one_mul, zero_mul, sub_zero, zero_add]
  | succ a ih =>
    intro b
    have h := ih (b + 1)
    rw [p_succ_succ b] at h
    rw [p_succ_succ a, show a + 1 + b + 1 = a + (b + 1) + 1 by omega, ← h]
    ring

end Aux_TLG34

open TemperleyLieb.Gram in
theorem solution :
    (∀ i j k : ℕ, j ≤ i → 1 ≤ k → k ≤ j →
      ∑ m ∈ Finset.Icc j i, p (2 * m) =
        p (i - k + 1) * p (i + k) - p (j - k) * p (j + k - 1)) ∧
    (∀ i j k : ℕ, j ≤ i → k ≤ j →
      ∑ m ∈ Finset.Icc j i, p (2 * m + 1) =
        p (i - k + 1) * p (i + k + 1) - p (j - k) * p (j + k)) := by
  refine ⟨fun i j k hji hk hkj => ?_, fun i j k hji hkj => ?_⟩
  · induction i, hji using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h := Aux_TLG34.key (j - k) (j + k - 1)
      rw [show j + k - 1 + 1 = j + k by omega, show j - k + (j + k - 1) + 1 = 2 * j by omega] at h
      exact h.symm
    | succ i hji ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have h := Aux_TLG34.key (i + 1 - k) (i + k)
      rw [show i + 1 - k + (i + k) + 1 = 2 * (i + 1) by omega,
        show i + 1 - k = i - k + 1 by omega] at h
      rw [show i + 1 - k + 1 = i - k + 1 + 1 by omega, show i + 1 + k = i + k + 1 by omega]
      linear_combination -h
  · induction i, hji using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h := Aux_TLG34.key (j - k) (j + k)
      rw [show j - k + (j + k) + 1 = 2 * j + 1 by omega] at h
      exact h.symm
    | succ i hji ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have h := Aux_TLG34.key (i + 1 - k) (i + k + 1)
      rw [show i + 1 - k + (i + k + 1) + 1 = 2 * (i + 1) + 1 by omega,
        show i + 1 - k = i - k + 1 by omega] at h
      rw [show i + 1 - k + 1 = i - k + 1 + 1 by omega, show i + 1 + k + 1 = i + k + 1 + 1 by omega]
      linear_combination -h
