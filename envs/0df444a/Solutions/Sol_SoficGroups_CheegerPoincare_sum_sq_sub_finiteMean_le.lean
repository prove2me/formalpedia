-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.sum_sq_sub_finiteMean_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/f6f79e77-0dcd-4002-a89d-1d8c49a4b5ce

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_sum_sub_finiteMean_eq_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.CheegerPoincare
open scoped BigOperators
namespace SoficGroups.CheegerPoincare
theorem _root_.solution {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (c : ℝ) :
    (∑ x : V, (f x - finiteMean f) ^ 2) ≤
      ∑ x : V, (f x - c) ^ 2 := by
  have hpoint (x : V) :
      (f x - c) ^ 2 =
        (f x - finiteMean f) ^ 2 +
          2 * (finiteMean f - c) * (f x - finiteMean f) +
          (finiteMean f - c) ^ 2 := by
    ring
  have hidentity :
      (∑ x : V, (f x - c) ^ 2) =
        (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
    calc
      (∑ x : V, (f x - c) ^ 2) =
          ∑ x : V,
            ((f x - finiteMean f) ^ 2 +
              2 * (finiteMean f - c) * (f x - finiteMean f) +
              (finiteMean f - c) ^ 2) :=
            Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          2 * (finiteMean f - c) *
            (∑ x : V, (f x - finiteMean f)) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∑ x : V, (f x - finiteMean f) ^ 2) +
          (Fintype.card V : ℝ) * (finiteMean f - c) ^ 2 := by
            rw [sum_sub_finiteMean_eq_zero]
            ring
  rw [hidentity]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
end SoficGroups.CheegerPoincare
