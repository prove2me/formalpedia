-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:59:42.801201+00:00
-- url     : https://prove2.me/submissions/2d0cbc43-db14-4c5b-b225-5dc239bd1647

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleLogGrowthBase_pos


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    0 < decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon := by
  unfold decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (routedDepthScheduleLogGrowthBase_pos epsilon hepsilon
        (decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
          epsilon hpool)) _)
end QEC.Distillation.HH18Parameterized
