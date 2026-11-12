-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthFreshParentAcceptedNextInput_eq_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:28:41.489208+00:00
-- url     : https://prove2.me/submissions/f9b5f9fd-bc7f-46ad-a047-fde01d1d82f6

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (source : BatchOutputPort × Fin resourceCount) :
    hh18DepthFreshParentAcceptedNextInput epsilon hsmall depth source =
      hh18AcceptedOutputAsNextInput (hh18ErrorIteration epsilon hsmall depth) := by
  rfl
end QEC.Distillation.HH18Protocol
