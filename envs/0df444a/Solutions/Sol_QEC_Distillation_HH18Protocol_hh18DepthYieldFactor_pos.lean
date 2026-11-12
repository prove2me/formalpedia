-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:27:23.621618+00:00
-- url     : https://prove2.me/submissions/bdaae585-583a-4323-8ffe-4f8f34f12cb5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos


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
    0 < (hh18DepthYieldFactor epsilon hsmall depth : ℝ) := by
  classical
  change 0 < ∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)
  exact Finset.prod_pos fun stage _ => rawSuccessMass_pos _
end QEC.Distillation.HH18Protocol
