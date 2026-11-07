-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toHermitianQubitOperator_commute_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:21.058522+00:00
-- url     : https://prove2.me/submissions/af6d5704-a535-4273-9c01-67ca02dd3787

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P Q : Binary ι) (h : Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      toHermitianQubitOperator Q * toHermitianQubitOperator P := by
  calc
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
        (hermitianPhaseScalar P * hermitianPhaseScalar Q) •
          (toQubitOperator P * toQubitOperator Q) := by
            exact smul_mul_smul_comm _ _ _ _
    _ = (hermitianPhaseScalar Q * hermitianPhaseScalar P) •
        (toQubitOperator Q * toQubitOperator P) := by
          rw [toQubitOperator_commute_of_commutes P Q h]
          rw [mul_comm (hermitianPhaseScalar P)]
    _ = toHermitianQubitOperator Q * toHermitianQubitOperator P := by
          exact (smul_mul_smul_comm _ _ _ _).symm
end QEC.Coding.PauliSymplectic
