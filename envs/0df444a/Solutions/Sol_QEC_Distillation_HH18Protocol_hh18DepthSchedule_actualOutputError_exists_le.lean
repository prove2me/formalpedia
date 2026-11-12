-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_actualOutputError_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:36:29.229314+00:00
-- url     : https://prove2.me/submissions/8f406d0c-40a9-4953-880b-8e6b7abc1f21

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_actualOutputError_le_targetError
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_targetError_exists_lt

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
    (hsmall : hh18InitialSmallDomain epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat,
      hh18DepthScheduleActualOutputError epsilon hsmall depth ≤ target := by
  obtain ⟨depth, hdepth⟩ :=
    hh18DepthSchedule_targetError_exists_lt epsilon hepsilon hsmall target htarget
  exact ⟨depth, (hh18DepthSchedule_actualOutputError_le_targetError
    epsilon hsmall depth).trans hdepth.le⟩
end QEC.Distillation.HH18Protocol
