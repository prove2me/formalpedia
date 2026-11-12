-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthYieldFactor_eq_actualStageSuccessProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:32:09.114752+00:00
-- url     : https://prove2.me/submissions/51e3aaf5-5877-4115-96eb-9240f0b88bbd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18ActualStageRun_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (hh18DepthYieldFactor epsilon hsmall depth : ℝ) =
      ∏ stage : Fin depth,
        (hh18ActualStageRun epsilon hsmall stage.1).successProbability := by
  classical
  change (∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1)) = _
  apply Finset.prod_congr rfl
  intro stage _
  exact (hh18ActualStageRun_successProbability epsilon hsmall stage.1).symm
end QEC.Distillation.HH18Protocol
