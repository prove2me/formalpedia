-- Prove2me | solution 1 for QuantumMaxCutEnergy.sum_load_eq_two_mul_internal_add_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:31:05.515242+00:00
-- url     : https://prove2.me/submissions/ae6ca6f8-41c2-44a9-afb7-c05fa4aac149

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Definitions.Def_QuantumMaxCutEdgeCrossSum
import Theorems.Thm_QuantumMaxCutEnergy_sum_ite_eq_of_mem
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **Double counting.** The load mass over `S` is twice the internal mass plus the mass leaving `S`. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) :
    2 * internalSum x S + crossSum x S = ∑ v ∈ S, loadAt x v := by
  classical
  -- the load side, split into the two endpoint contributions
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
          by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;> simp [h1, h2]
  rw [hswap]
  -- the internal/crossing side, as one sum
  have hi : (∑ e : Edge n, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0))
      = internalSum x S := by
    rw [internalSum, ← Finset.sum_filter]
  have hc : (∑ e : Edge n,
      (if (e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S) then x e else 0))
      = crossSum x S := by
    rw [crossSum, ← Finset.sum_filter]
  have hL : 2 * internalSum x S + crossSum x S
      = ∑ e : Edge n, (2 * (if e.val.1 ∈ S ∧ e.val.2 ∈ S then x e else 0)
          + (if (e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S) then x e else 0)) := by
    rw [← hi, ← hc, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hL]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S <;>
    simp [h1, h2] <;> ring

#print axioms solution
