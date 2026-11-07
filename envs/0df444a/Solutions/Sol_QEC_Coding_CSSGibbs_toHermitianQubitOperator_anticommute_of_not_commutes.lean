-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.toHermitianQubitOperator_anticommute_of_not_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:10.000208+00:00
-- url     : https://prove2.me/submissions/dbb3473c-40a8-41b3-987e-c0d6a05543c9

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.CSSGibbs
theorem _root_.solution
    (P Q : Binary ι) (h : ¬ Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      -(toHermitianQubitOperator Q * toHermitianQubitOperator P) := by
  unfold toHermitianQubitOperator
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  rw [toQubitOperator_anticommute_of_not_commutes P Q h]
  module
end QEC.Coding.CSSGibbs
