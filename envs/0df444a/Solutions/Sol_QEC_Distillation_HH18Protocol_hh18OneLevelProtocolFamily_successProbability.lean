-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_successProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:29:54.565199+00:00
-- url     : https://prove2.me/submissions/0af7c119-c7f5-4ec6-9ada-4474e8564fcd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_eq_rawSuccessMass


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
    ((hh18OneLevelProtocolFamily epsilon).protocol PUnit.unit).run.successProbability =
      rawSuccessMass epsilon := by
  change endpointWeight (noisyResources epsilon) .accepted = rawSuccessMass epsilon
  exact endpointWeight_accepted_eq_rawSuccessMass epsilon
end QEC.Distillation.HH18Protocol
