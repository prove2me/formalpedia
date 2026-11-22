-- Prove2me | solution 1 for QEC.Distillation.bk05TCompleteSemanticSchedule_protocol_reportedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T23:12:53.975733+00:00
-- url     : https://prove2.me/submissions/c010fe78-e47e-40a5-ba60-d2bc69f3cf42

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
import Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK05T_fiveQubitDistillationRun_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK05T_fiveQubitMagicStateProtocol_reportedOutput

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
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).run.reportedOutput
        (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).behavior := by
  calc
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput :=
      bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
        rho hthreshold depth
    _ = BK05T.fiveQubitAcceptedOutput (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth) :=
      BK05T.fiveQubitDistillationRun_acceptedOutput _ _ _
    _ = (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).run.reportedOutput
        (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).behavior :=
      (BK05T.fiveQubitMagicStateProtocol_reportedOutput _ _ _).symm
end QEC.Distillation
