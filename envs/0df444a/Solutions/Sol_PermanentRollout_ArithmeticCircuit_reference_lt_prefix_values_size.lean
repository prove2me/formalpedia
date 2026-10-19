-- Prove2me | solution 1 for PermanentRollout.ArithmeticCircuit.reference_lt_prefix_values_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/eab94268-ca39-4f2e-bf5e-676418e8164a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_size
import Theorems.Thm_PermanentRollout_CircuitInstructionReference_lt_of_referencesBounded
import Theorems.Thm_PermanentRollout_CircuitPrefix_forwardFold_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.ArithmeticCircuit
namespace PermanentRollout.ArithmeticCircuit
theorem _root_.solution {ι : Type}
    (circuit : ArithmeticCircuit ι) (position : Fin circuit.program.length)
    (index : ℕ)
    (hreference : CircuitInstructionReference
      (circuit.program.get position) index) :
    index <
      ((circuit.program.take position.val).foldl
        (fun values instruction => values.push (instruction.eval values))
        (#[] : Array (MvPolynomial ι ℂ))).size := by
  have hindex : index < position.val :=
    hreference.lt_of_referencesBounded (circuit.valid position)
  have hsize := CircuitPrefix.forwardFold_size
    (circuit.program.take position.val)
    (#[] : Array (MvPolynomial ι ℂ))
  simp only [Array.size_empty, zero_add, List.length_take] at hsize
  rw [hsize, Nat.min_eq_left (Nat.le_of_lt position.isLt)]
  exact hindex
end PermanentRollout.ArithmeticCircuit
