-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_one_eq_oneLevelYieldFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:31:04.930731+00:00
-- url     : https://prove2.me/submissions/a4e8ae59-ef91-4c6e-a597-df3688f984b0

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) :
    (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
      (oneLevelYieldFactor epsilon : ℝ) := by
  change (∏ stage : Fin 1,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) =
      oneLevelExpectedYield epsilon
  rw [Fin.prod_univ_one]
  change rawSuccessMass epsilon = oneLevelExpectedYield epsilon
  rw [oneLevelExpectedYield_eq_success,
    endpointWeight_accepted_eq_rawSuccessMass]
end QEC.Distillation.HH18Protocol
