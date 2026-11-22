-- Prove2me | solution 1 for QEC.Distillation.bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T23:06:52.484249+00:00
-- url     : https://prove2.me/submissions/d0cd3849-dd8d-4a44-851b-5d131d2236a3

import Theorems.Thm_QEC_Distillation_BK05T_fiveQubitDistillationRun_acceptedOutput
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality

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
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput := by
  change BK05T.fiveQubitAcceptedOutput (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth) =
    (BK05T.fiveQubitDistillationRun (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).acceptedOutput
  exact (BK05T.fiveQubitDistillationRun_acceptedOutput _ _ _).symm
end QEC.Distillation
