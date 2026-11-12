-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSuccessfulOutputCost_le_constant_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:41:12.141797+00:00
-- url     : https://prove2.me/submissions/ce7d5da0-418b-4b1b-9a7e-4a83800c515c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthYieldFactor_lower_bound
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
    hh18DepthSuccessfulOutputCost epsilon hsmall depth ≤ 2 * (15 : ℝ) ^ depth := by
  rw [hh18DepthSuccessfulOutputCost_eq]
  have hratioNonneg : 0 ≤ (15 : ℝ) ^ depth := by positivity
  have hyieldHalf : (1 : ℝ) / 2 ≤
      (hh18DepthYieldFactor epsilon hsmall depth : ℝ) :=
    hh18DepthYieldFactor_lower_bound epsilon hsmall depth
  calc
    (15 : ℝ) ^ depth / (hh18DepthYieldFactor epsilon hsmall depth : ℝ) ≤
        (15 : ℝ) ^ depth / ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyieldHalf
    _ = 2 * (15 : ℝ) ^ depth := by ring
end QEC.Distillation.HH18Protocol
