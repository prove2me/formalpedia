-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.oneLevelSuccessfulOutputCost_eq_fifteen_div_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:32:51.969081+00:00
-- url     : https://prove2.me/submissions/5b0d8e6b-03bc-4b18-83b7-a36a95a96b32

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelInputOutputRatio_eq_fifteen

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelSuccessfulOutputCost epsilon =
      15 / endpointWeight (noisyResources epsilon) .accepted := by
  unfold oneLevelSuccessfulOutputCost DependentBatch.typedSuccessfulOutputCost
  change oneLevelInputOutputRatio / (oneLevelYieldFactor epsilon : ℝ) = _
  rw [oneLevelInputOutputRatio_eq_fifteen]
  change 15 / oneLevelExpectedYield epsilon = _
  rw [oneLevelExpectedYield_eq_success]
end QEC.Distillation.HH18Protocol
