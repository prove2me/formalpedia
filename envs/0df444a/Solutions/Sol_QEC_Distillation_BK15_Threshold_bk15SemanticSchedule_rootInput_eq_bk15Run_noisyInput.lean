-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:40:39.355156+00:00
-- url     : https://prove2.me/submissions/35ad6c56-1304-453e-af50-ea9cf52c2ebe

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput := by
  funext site
  change aBasisDephasing.mapDensity
      (BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold depth)) =
    diagonalAResource
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
  exact bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
    rho hpositive hthreshold depth
end QEC.Distillation.BK15.Threshold
