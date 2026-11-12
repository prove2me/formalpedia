-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_one_eq_oneLevelSuccessfulOutputCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:36:23.699933+00:00
-- url     : https://prove2.me/submissions/63807ed5-3f62-4e18-855c-437e996e3209

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_eq
import Theorems.Thm_QEC_Distillation_HH18Protocol_oneLevelSuccessfulOutputCost_eq_fifteen_div_success
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_one_eq_oneLevelYieldFactor

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
    hh18DepthSuccessfulOutputCost epsilon hsmall 1 =
      oneLevelSuccessfulOutputCost epsilon := by
  rw [hh18DepthSuccessfulOutputCost_eq,
    oneLevelSuccessfulOutputCost_eq_fifteen_div_success]
  have hyield :
      (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
        endpointWeight (noisyResources epsilon) .accepted := by
    calc
      (hh18DepthYieldFactor epsilon hsmall 1 : ℝ) =
          (oneLevelYieldFactor epsilon : ℝ) :=
        hh18DepthYieldFactor_one_eq_oneLevelYieldFactor epsilon hsmall
      _ = oneLevelExpectedYield epsilon := rfl
      _ = endpointWeight (noisyResources epsilon) .accepted :=
        oneLevelExpectedYield_eq_success epsilon
  rw [hyield]
  norm_num
end QEC.Distillation.HH18Protocol
