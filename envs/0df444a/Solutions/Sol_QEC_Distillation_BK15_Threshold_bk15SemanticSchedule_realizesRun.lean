-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_realizesRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:46:09.38643+00:00
-- url     : https://prove2.me/submissions/2725d37b-5db9-4dd9-bc38-81d1b773dad3

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_root_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput

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
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 ∧
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
    BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput := by
  exact ⟨bk15SemanticSchedule_root_resourceCount rho hpositive hthreshold depth,
    bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput rho hpositive hthreshold depth,
    bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
      rho hpositive hthreshold depth,
    bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
      rho hpositive hthreshold depth⟩
end QEC.Distillation.BK15.Threshold
