-- Prove2me | solution 1 for PermanentRollout.freeAffineCircuitGraphEvaluation_extendedForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/309d0daf-be2a-4e61-9911-261eb84df9f7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_reference

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (form : FreeAffineForm (Fin k)) :
    freeAffineCircuitGraphEvaluation circuit
      (freeAffineExtendedForm
        (n := circuit.program.length) form) =
      form.eval circuit.values := by
  classical
  simp [freeAffineExtendedForm, FreeAffineForm.eval,
    Finsupp.linearCombination_apply, Finsupp.sum,
    freeAffineCircuitGraphEvaluation,
    MvPolynomial.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simpa [freeAffineCircuitGraphEvaluation,
    MvPolynomial.aeval_def, Array.getD_eq_getD_getElem?] using
    freeAffineCircuitGraphEvaluation_reference circuit r
end PermanentRollout
