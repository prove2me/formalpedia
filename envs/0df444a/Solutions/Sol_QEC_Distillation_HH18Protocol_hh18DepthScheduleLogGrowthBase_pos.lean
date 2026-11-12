-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleLogGrowthBase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:46:33.585195+00:00
-- url     : https://prove2.me/submissions/2fd51c40-e321-4089-b403-d75f57512ef0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    0 < hh18DepthScheduleLogGrowthBase epsilon := by
  unfold hh18DepthScheduleLogGrowthBase
  apply neg_pos.mpr
  apply Real.log_neg
  · exact mul_pos hh18IterationScale_pos hepsilon
  · exact hsmall.trans_lt (by norm_num)
end QEC.Distillation.HH18Protocol
