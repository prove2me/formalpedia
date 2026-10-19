-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitInstructionEquation_degree_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/6f774897-6e33-4b11-8439-0935bf85c930

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineCircuitInstructionEquation_totalDegree_le
import Theorems.Thm_PermanentRollout_freeAffineInstruction_program_cost_product

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k)) :
    (∏ j : Fin circuit.program.length,
      (freeAffineCircuitInstructionEquation circuit j).totalDegree) ≤
      2 ^ circuit.multiplicationCount := by
  classical
  calc
    (∏ j : Fin circuit.program.length,
      (freeAffineCircuitInstructionEquation circuit j).totalDegree) ≤
      ∏ j : Fin circuit.program.length,
        if (circuit.program.get j).isMultiplication then (2 : ℕ) else 1 := by
          apply Finset.prod_le_prod'
          intro j _
          exact freeAffineCircuitInstructionEquation_totalDegree_le
            circuit j
    _ = (circuit.program.map fun instruction =>
        if instruction.isMultiplication then (2 : ℕ) else 1).prod := by
          exact Fin.prod_univ_fun_getElem circuit.program
            (fun instruction =>
              if instruction.isMultiplication then (2 : ℕ) else 1)
    _ = 2 ^ circuit.multiplicationCount :=
      freeAffineInstruction_program_cost_product circuit.program
end PermanentRollout
