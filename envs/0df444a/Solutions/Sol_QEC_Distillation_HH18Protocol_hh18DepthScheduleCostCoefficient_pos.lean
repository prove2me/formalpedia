-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleCostCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:32:58.394929+00:00
-- url     : https://prove2.me/submissions/dbf39db5-ccf4-4a65-8f61-0989bf689741

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleLogGrowthBase_pos

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
    0 < hh18DepthScheduleCostCoefficient epsilon := by
  unfold hh18DepthScheduleCostCoefficient
  exact div_pos (by norm_num)
    (Real.rpow_pos_of_pos
      (hh18DepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall) _)
end QEC.Distillation.HH18Protocol
