-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthRoutedChildRun_eq_actualStageRun_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:32:59.386222+00:00
-- url     : https://prove2.me/submissions/f8d43144-a65c-4c84-b14d-76ef5e18c585

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthRoutedChildResources_eq_stageResource_succ

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
    hh18DepthRoutedChildRun epsilon hsmall depth =
      hh18ActualStageRun epsilon hsmall (depth + 1) := by
  unfold hh18DepthRoutedChildRun hh18ActualStageRun
  rw [hh18DepthRoutedChildResources_eq_stageResource_succ]
  rfl
end QEC.Distillation.HH18Protocol
