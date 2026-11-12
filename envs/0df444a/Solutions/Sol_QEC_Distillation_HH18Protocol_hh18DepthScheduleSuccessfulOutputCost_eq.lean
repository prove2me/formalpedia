-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:36:17.566254+00:00
-- url     : https://prove2.me/submissions/b2e65153-78ee-4c01-8425-7964b7035fa9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_eq

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) =
        (15 : ℝ) ^ depth /
          (hh18DepthScheduleYieldFactor epsilon hsmall depth : ℝ) :=
  hh18DepthSuccessfulOutputCost_eq epsilon hsmall depth
end QEC.Distillation.HH18Protocol
