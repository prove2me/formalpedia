-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:35:29.693068+00:00
-- url     : https://prove2.me/submissions/fa7ae45e-1e7c-4fec-9479-0d12273d13df

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18ActualStageRun_successProbability
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_eq
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_succ_actualStageRun
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
    hh18DepthSuccessfulOutputCost epsilon hsmall (depth + 1) =
      15 * hh18DepthSuccessfulOutputCost epsilon hsmall depth /
        rawSuccessMass (hh18ErrorIteration epsilon hsmall depth) := by
  rw [← hh18ActualStageRun_successProbability epsilon hsmall depth]
  rw [hh18DepthSuccessfulOutputCost_eq,
    hh18DepthSuccessfulOutputCost_eq,
    hh18DepthYieldFactor_succ_actualStageRun]
  have hyield : (hh18DepthYieldFactor epsilon hsmall depth : ℝ) ≠ 0 :=
    ne_of_gt (hh18DepthYieldFactor_pos epsilon hsmall depth)
  have hsuccess : (hh18ActualStageRun epsilon hsmall depth).successProbability ≠ 0 :=
    ne_of_gt (by
      rw [hh18ActualStageRun_successProbability]
      exact rawSuccessMass_pos _)
  rw [pow_succ]
  field_simp [hyield, hsuccess]
end QEC.Distillation.HH18Protocol
