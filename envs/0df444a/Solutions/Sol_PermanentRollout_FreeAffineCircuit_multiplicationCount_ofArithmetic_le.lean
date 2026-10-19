-- Prove2me | solution 1 for PermanentRollout.FreeAffineCircuit.multiplicationCount_ofArithmetic_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/9df72e93-73e6-454f-a084-5b0eb33137c4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.FreeAffineCircuit
namespace PermanentRollout.FreeAffineCircuit
theorem _root_.solution {ι : Type}
    (circuit : ArithmeticCircuit ι) :
    (ofArithmetic circuit).multiplicationCount ≤ circuit.size := by
  change
    ((circuit.program.map FreeAffineInstruction.ofInstruction).filter
      FreeAffineInstruction.isMultiplication).length ≤
      (circuit.program.filter Instruction.isArithmetic).length
  induction circuit.program with
  | nil => simp
  | cons instruction tail ih =>
    cases instruction <;>
      simp [FreeAffineInstruction.ofInstruction,
        FreeAffineInstruction.isMultiplication, Instruction.isArithmetic] at * <;>
      omega
end PermanentRollout.FreeAffineCircuit
