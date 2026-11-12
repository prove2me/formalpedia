-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:44:14.626645+00:00
-- url     : https://prove2.me/submissions/5e9eef77-a3d7-40f4-be52-e6094f29eb77

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSuccessfulOutputCost_le_constant_mul_pow
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow

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
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma := by
  rw [hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow]
  exact hh18DepthSuccessfulOutputCost_le_constant_mul_pow epsilon hsmall depth
end QEC.Distillation.HH18Protocol
