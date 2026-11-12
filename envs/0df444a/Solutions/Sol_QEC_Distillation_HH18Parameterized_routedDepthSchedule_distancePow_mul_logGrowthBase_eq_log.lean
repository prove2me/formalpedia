-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:13:59.08536+00:00
-- url     : https://prove2.me/submissions/03c63dd8-6e01-4230-8a4c-bd4406551a42

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hepsilon : 0 < epsilon.1) (depth : Nat) :
    (codeDistance r w : ℝ) ^ depth *
        routedDepthScheduleLogGrowthBase w r m epsilon =
      Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth) := by
  have hbase : 0 < routedDepthIterationScale w r m * epsilon.1 :=
    mul_pos (routedDepthIterationScale_pos w r m) hepsilon
  unfold routedDepthScheduleTargetError
  rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hbase _)), Real.log_one,
    Real.log_pow]
  push_cast
  unfold routedDepthScheduleLogGrowthBase
  ring
end QEC.Distillation.HH18Parameterized
