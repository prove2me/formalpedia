-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendReverseProducts_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/d663939c-3dfe-4183-93c6-fbd7151687e9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_values_size
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendInstruction_values

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
    (hright : right < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).values =
      ((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values * circuit.values.getD right 0)).push
          (adjoint.eval circuit.values * circuit.values.getD left 0) := by
  have hfirst :
      (circuit.values.push (adjoint.eval circuit.values)).getD
        circuit.program.length 0 = adjoint.eval circuit.values := by
    rw [← circuit_values_size circuit]
    simp [Array.getD_eq_getD_getElem?]
  have hrightFirst :
      (circuit.values.push (adjoint.eval circuit.values)).getD right 0 =
        circuit.values.getD right 0 := by
    have hne : right ≠ circuit.values.size := by
      rw [circuit_values_size]
      exact Nat.ne_of_lt hright
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hne]
  have hsecond :
      ((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).getD circuit.program.length 0 =
        adjoint.eval circuit.values := by
    have hne : circuit.program.length ≠
        (circuit.values.push (adjoint.eval circuit.values)).size := by
      simp [circuit_values_size]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push,
      if_neg hne]
    simpa only [Array.getD_eq_getD_getElem?] using hfirst
  have hleftSecond :
      ((circuit.values.push (adjoint.eval circuit.values)).push
        (adjoint.eval circuit.values *
          circuit.values.getD right 0)).getD left 0 =
        circuit.values.getD left 0 := by
    have hleftFirst : left ≠ circuit.values.size := by
      rw [circuit_values_size]
      exact Nat.ne_of_lt hleft
    have hleftNext : left ≠ circuit.values.size + 1 := by
      rw [circuit_values_size]
      omega
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push,
      hleftFirst, hleftNext]
  simp only [appendReverseProducts, appendInstruction_values,
    FreeAffineInstruction.eval, hfirst, hrightFirst, hsecond,
    hleftSecond]
end PermanentRollout.ReverseAdjoint
