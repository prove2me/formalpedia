-- Prove2me | solution 1 for ThornStringBits.chainPotential_eq_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:38:48.168337+00:00
-- url     : https://prove2.me/submissions/e2f07783-b96c-4c7f-a49f-a3fa6ecf217e

import Mathlib
import Definitions.Def_ThornStringBits_Defs

set_option autoImplicit false

open Real Matrix ThornStringBits in
theorem solution (M : ℕ) (x : Fin M → ℝ) :
    chainPotential M x = x ⬝ᵥ (cycLaplacian M *ᵥ x) := by
  cases M with
  | zero => simp [chainPotential]
  | succ n =>
    set e : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1) with he
    have hs : ∀ i : Fin (n + 1), (⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        : Fin (n + 1)) = e i := by
      intro i
      ext
      rw [he, finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    have hL : ∀ i j : Fin (n + 1), cycLaplacian (n + 1) i j =
        (if i = j then 2 else 0) - (if j = e i then 1 else 0) - (if i = e j then 1 else 0) := by
      intro i j
      unfold cycLaplacian
      have c1 : (j.val = (i.val + 1) % (n + 1)) ↔ j = e i := by rw [← hs i, Fin.ext_iff]
      have c2 : (i.val = (j.val + 1) % (n + 1)) ↔ i = e j := by rw [← hs j, Fin.ext_iff]
      simp only [c1, c2]
    have hrow : ∀ i, (cycLaplacian (n + 1) *ᵥ x) i = 2 * x i - x (e i) - x (e.symm i) := by
      intro i
      have h1 : ∑ j, (if i = j then (2:ℝ) else 0) * x j = 2 * x i := by
        simp [ite_mul]
      have h2 : ∑ j, (if j = e i then (1:ℝ) else 0) * x j = x (e i) := by
        simp [ite_mul]
      have h3 : ∑ j, (if i = e j then (1:ℝ) else 0) * x j = x (e.symm i) := by
        have : ∀ j, (i = e j) ↔ (e.symm i = j) := fun j => by rw [Equiv.symm_apply_eq]
        simp [ite_mul, this]
      simp only [Matrix.mulVec, dotProduct, hL, sub_mul, Finset.sum_sub_distrib]
      rw [h1, h2, h3]
    unfold chainPotential
    simp only [hs]
    rw [dotProduct]
    simp only [hrow]
    have hA : ∑ i, x (e i) ^ 2 = ∑ i, x i ^ 2 := Equiv.sum_comp e (fun i => x i ^ 2)
    have hB : ∑ i, x i * x (e.symm i) = ∑ i, x (e i) * x i := by
      rw [← Equiv.sum_comp e (fun i => x i * x (e.symm i))]
      simp
    have expand1 : ∑ i, (x (e i) - x i) ^ 2
        = ∑ i, x (e i) ^ 2 - 2 * ∑ i, x (e i) * x i + ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have expand2 : ∑ i, x i * (2 * x i - x (e i) - x (e.symm i))
        = 2 * ∑ i, x i ^ 2 - ∑ i, x (e i) * x i - ∑ i, x i * x (e.symm i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [expand1, expand2, hA, hB]
    ring
