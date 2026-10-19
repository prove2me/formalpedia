-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/85fc07ac-4e5e-4cd2-91ea-44178ebe6370

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {V : Type*} [Fintype V]
    (f : V → ℝ) (p q : Equiv.Perm V) :
    squaredPermutationEnergy f (p * q) ≤
      2 * squaredPermutationEnergy f p +
        2 * squaredPermutationEnergy f q := by
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f ((p * q) x) - f x) ^ 2) ≤
        ∑ x : V,
          (2 * (f (p (q x)) - f (q x)) ^ 2 +
           2 * (f (q x) - f x) ^ 2) := by
      apply Finset.sum_le_sum
      intro x _
      simp only [Equiv.Perm.mul_apply]
      nlinarith [sq_nonneg
        ((f (p (q x)) - f (q x)) - (f (q x) - f x))]
    _ = 2 * (∑ x : V, (f (p x) - f x) ^ 2) +
          2 * (∑ x : V, (f (q x) - f x) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Equiv.sum_comp q (fun x : V => (f (p x) - f x) ^ 2)]
end SoficGroups.KunPositiveWordMidrankEnergy
