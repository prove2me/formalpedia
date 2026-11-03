-- Prove2me | solution 1 for QuantumMaxCutEnergy.internalSum_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:08:16.422759+00:00
-- url     : https://prove2.me/submissions/7d64bbe6-10a8-4b27-837a-5129a5df9485

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **Uncrossing identity.** For nonnegative `x` and any two vertex sets, the internal masses add up to at
most the internal masses of the union and the intersection: the edges crossing between `A \ B` and `B \ A`
are counted on the right but not on the left. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (A B : Finset (Fin n)) :
    internalSum x A + internalSum x B ≤ internalSum x (A ∪ B) + internalSum x (A ∩ B) := by
  classical
  have hpt : ∀ e : Edge n,
      (if e.val.1 ∈ A ∧ e.val.2 ∈ A then x e else 0) + (if e.val.1 ∈ B ∧ e.val.2 ∈ B then x e else 0)
        ≤ (if e.val.1 ∈ A ∪ B ∧ e.val.2 ∈ A ∪ B then x e else 0)
          + (if e.val.1 ∈ A ∩ B ∧ e.val.2 ∈ A ∩ B then x e else 0) := by
    intro e
    by_cases h1 : e.val.1 ∈ A <;> by_cases h2 : e.val.2 ∈ A <;>
      by_cases h3 : e.val.1 ∈ B <;> by_cases h4 : e.val.2 ∈ B <;>
      simp only [h1, h2, h3, h4, Finset.mem_union, Finset.mem_inter, and_self, and_false,
        false_and, or_self, or_false, false_or, if_true, if_false, not_false_eq_true, and_true,
        true_and] <;>
      first
        | (exfalso; tauto)
        | nlinarith [hx e]
  have hsum : ∑ e : Edge n, ((if e.val.1 ∈ A ∧ e.val.2 ∈ A then x e else 0)
        + (if e.val.1 ∈ B ∧ e.val.2 ∈ B then x e else 0))
      ≤ ∑ e : Edge n, ((if e.val.1 ∈ A ∪ B ∧ e.val.2 ∈ A ∪ B then x e else 0)
        + (if e.val.1 ∈ A ∩ B ∧ e.val.2 ∈ A ∩ B then x e else 0)) :=
    Finset.sum_le_sum (fun e _ => hpt e)
  simp only [Finset.sum_add_distrib] at hsum
  rw [internalSum, internalSum, internalSum, internalSum]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  exact hsum

#print axioms solution
