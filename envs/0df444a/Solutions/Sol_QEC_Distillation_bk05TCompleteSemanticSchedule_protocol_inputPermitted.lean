-- Prove2me | solution 1 for QEC.Distillation.bk05TCompleteSemanticSchedule_protocol_inputPermitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T22:55:19.411034+00:00
-- url     : https://prove2.me/submissions/406906c4-da4f-4c47-b72e-dbcfad01b692

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
import Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput

set_option autoImplicit false
noncomputable section
universe u v
open QEC
open QEC.Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise
namespace QEC.Distillation
theorem _root_.solution
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).inputErrorModel.Permits
      (BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1))) := by
  rw [bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput rho hthreshold depth]
  exact (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
    (tIteration_bounds rho hthreshold depth).1
    (tIteration_le_one rho hthreshold depth)).inputPermitted
end QEC.Distillation
