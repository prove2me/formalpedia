-- Prove2me | solution 1 for QuantumMaxCutEnergy.tight_odd_cross_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:31:06.245938+00:00
-- url     : https://prove2.me/submissions/b9e825ac-c3f4-4327-927c-c73e510f80c3

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Definitions.Def_QuantumMaxCutEdgeCrossSum
import Theorems.Thm_QuantumMaxCutEnergy_sum_ite_eq_of_mem
import Theorems.Thm_QuantumMaxCutEnergy_sum_load_eq_two_mul_internal_add_cross
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **A tight odd set sends at most one unit of mass outside itself.** -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hload : ∀ v, loadAt x v ≤ 1)
    (S : Finset (Fin n)) (htight : internalSum x S = ((S.card : ℝ) - 1) / 2) :
    crossSum x S ≤ 1 := by
  have hid := sum_load_eq_two_mul_internal_add_cross x S
  have h2 : ∑ v ∈ S, loadAt x v ≤ (S.card : ℝ) := by
    have h3 : ∑ v ∈ S, loadAt x v ≤ ∑ v ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hload v)
    simpa [Finset.sum_const, nsmul_eq_mul] using h3
  rw [htight] at hid
  linarith

#print axioms solution
