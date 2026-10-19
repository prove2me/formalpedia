-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendReverseProducts_values_getD_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/7e780c16-e92c-4e3a-a401-d093a879c3f8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_values_size
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length)
    (index : ℕ) (hindex : index < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).values.getD index 0 =
        circuit.values.getD index 0 := by
  have hzero : index ≠ circuit.values.size := by
    rw [circuit_values_size]
    omega
  have hone : index ≠ circuit.values.size + 1 := by
    rw [circuit_values_size]
    omega
  have htwo : index ≠ circuit.values.size + 1 + 1 := by
    rw [circuit_values_size]
    omega
  rw [appendReverseProducts_values]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push,
    hzero, hone, htwo]
end PermanentRollout.ReverseAdjoint
