-- Prove2me | solution 1 for QEC.Distillation.bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T22:31:11.767348+00:00
-- url     : https://prove2.me/submissions/4af18a06-302a-4bb0-bb44-23d58e3e4cb1

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
import Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput

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
    BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).noisyInput := by
  funext site
  change BK05TSemanticSchedule.rootOutput
      (bk05TCompleteSemanticSchedule rho hthreshold depth) =
    BK05T.tDiagonalInput (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)
  exact bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
    rho hthreshold depth
end QEC.Distillation
