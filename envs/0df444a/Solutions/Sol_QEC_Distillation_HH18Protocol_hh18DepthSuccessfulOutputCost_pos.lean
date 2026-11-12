-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:32:38.395205+00:00
-- url     : https://prove2.me/submissions/59fa31fd-ca6e-4cc4-9f94-efbcdf1fea11

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_pos
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
    0 < hh18DepthSuccessfulOutputCost epsilon hsmall depth := by
  rw [hh18DepthSuccessfulOutputCost_eq]
  exact div_pos (by positivity) (hh18DepthYieldFactor_pos epsilon hsmall depth)
end QEC.Distillation.HH18Protocol
