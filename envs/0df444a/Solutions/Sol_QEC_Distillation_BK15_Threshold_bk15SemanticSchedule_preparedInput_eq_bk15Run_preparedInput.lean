-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:43:23.066858+00:00
-- url     : https://prove2.me/submissions/f5aa893a-52b7-461c-b3fc-70cac38595a7

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput

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
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) := by
  change bk15PrepareInput
      (BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) =
    bk15PrepareInput
      ((bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput)
  rw [bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
    rho hpositive hthreshold depth]
end QEC.Distillation.BK15.Threshold
