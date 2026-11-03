-- Prove2me | solution 1 for QuantumMaxCutEnergy.sum_ite_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:33:41.123678+00:00
-- url     : https://prove2.me/submissions/27829b48-3fd7-4675-8e75-201b7d9a8831

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- A single-coordinate indicator sum. -/
theorem solution {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (c : ℝ) :
    ∑ v ∈ S, (if v = a then c else 0) = if a ∈ S then c else 0 := by
  classical
  by_cases ha : a ∈ S
  · rw [if_pos ha, Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd ha h
  · rw [if_neg ha]
    exact Finset.sum_eq_zero (fun v hv => by
      by_cases hv' : v = a
      · exact absurd (hv' ▸ hv) ha
      · simp [hv'])

#print axioms solution
