-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleLogGrowthBase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:50:50.093719+00:00
-- url     : https://prove2.me/submissions/95b29442-bf71-4c0c-b351-6d4440606807

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
theorem _root_.solution {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    0 < routedDepthScheduleLogGrowthBase w r m epsilon := by
  unfold routedDepthScheduleLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos (routedDepthIterationScale_pos w r m) hepsilon
  · exact hsmall.trans_lt (by norm_num)
end QEC.Distillation.HH18Parameterized
