-- Prove2me | solution 1 for QuantumMaxCutEnergy.tight_cross_eq_one_sub_deficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:31:07.066219+00:00
-- url     : https://prove2.me/submissions/fe74d020-da90-47d4-8c54-2bd57533b9c7

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

/-- **Exact form**: the mass leaving a tight set is one minus the total deficit inside it. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hload : ∀ v, loadAt x v ≤ 1)
    (S : Finset (Fin n)) (htight : internalSum x S = ((S.card : ℝ) - 1) / 2) :
    crossSum x S = 1 - ∑ v ∈ S, (1 - loadAt x v) := by
  have hid := sum_load_eq_two_mul_internal_add_cross x S
  have hdef : ∑ v ∈ S, (1 - loadAt x v) = (S.card : ℝ) - ∑ v ∈ S, loadAt x v := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [htight] at hid
  rw [hdef]
  linarith

#print axioms solution
