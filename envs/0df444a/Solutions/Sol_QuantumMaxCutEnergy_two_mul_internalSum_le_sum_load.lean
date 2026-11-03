-- Prove2me | solution 1 for QuantumMaxCutEnergy.two_mul_internalSum_le_sum_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:33:41.81131+00:00
-- url     : https://prove2.me/submissions/845105d2-ed96-4413-8568-d12d6aea6437

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
import Theorems.Thm_QuantumMaxCutEnergy_sum_ite_eq_of_mem

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- The load mass of a vertex set is at least twice its internal edge mass. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin n)) :
    2 * internalSum x S ≤ ∑ v ∈ S, loadAt x v := by
  classical
  -- split each load into its two endpoint contributions
  have hinner : ∀ v : Fin n, loadAt x v
      = ∑ e : Edge n, ((if v = e.val.1 then x e else 0) + (if v = e.val.2 then x e else 0)) := by
    intro v
    rw [loadAt]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    by_cases h1 : v = e.val.1
    · have h2 : v ≠ e.val.2 := by rw [h1]; exact hne
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : v = e.val.2
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg (by tauto : ¬ (v = e.val.1 ∨ v = e.val.2)), if_neg h1, if_neg h2, add_zero]
  have hswap : ∑ v ∈ S, loadAt x v
      = ∑ e : Edge n, (x e * (if e.val.1 ∈ S then (1:ℝ) else 0)
          + x e * (if e.val.2 ∈ S then (1:ℝ) else 0)) := by
    calc ∑ v ∈ S, loadAt x v
        = ∑ v ∈ S, ∑ e : Edge n,
            ((if v = e.val.1 then x e else 0) + (if v = e.val.2 then x e else 0)) :=
          Finset.sum_congr rfl (fun v _ => hinner v)
      _ = ∑ e : Edge n, ∑ v ∈ S,
            ((if v = e.val.1 then x e else 0) + (if v = e.val.2 then x e else 0)) :=
          Finset.sum_comm
      _ = ∑ e : Edge n, (x e * (if e.val.1 ∈ S then (1:ℝ) else 0)
            + x e * (if e.val.2 ∈ S then (1:ℝ) else 0)) := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [Finset.sum_add_distrib, sum_ite_eq_of_mem S e.val.1 (x e),
            sum_ite_eq_of_mem S e.val.2 (x e)]
          by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;>
            simp [h1, h2, mul_comm]
  have hpt2 : ∀ e : Edge n, 2 * (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0)
      ≤ x e * (if e.val.1 ∈ S then (1:ℝ) else 0) + x e * (if e.val.2 ∈ S then (1:ℝ) else 0) := by
    intro e
    by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;> simp [h1, h2] <;> linarith [hx e]
  have hi : (∑ e : Edge n, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0))
      = internalSum x S := by
    rw [internalSum, ← Finset.sum_filter]
  calc 2 * internalSum x S
      = 2 * ∑ e : Edge n, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0) := by rw [hi]
    _ = ∑ e : Edge n, 2 * (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ e : Edge n, (x e * (if e.val.1 ∈ S then (1:ℝ) else 0)
          + x e * (if e.val.2 ∈ S then (1:ℝ) else 0)) := Finset.sum_le_sum (fun e _ => hpt2 e)
    _ = ∑ v ∈ S, loadAt x v := hswap.symm

#print axioms solution
