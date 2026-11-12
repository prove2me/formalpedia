-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_targetError_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:36:14.236751+00:00
-- url     : https://prove2.me/submissions/4f9f082f-281f-4871-ac20-5df1462132f0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18CubicErrorEnvelope_closed_form
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_targetError_pos
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
private theorem hh18DepthSchedule_residualCoefficient_nonneg :
    0 ≤ residualCubicCoefficient := by
  unfold residualCubicCoefficient
  positivity
private theorem hh18DepthScheduleScale_one_le : 1 ≤ hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [hh18DepthSchedule_residualCoefficient_nonneg]
end HH18Protocol
end Distillation
end QEC
end
end

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
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    hh18DepthScheduleTargetError epsilon depth < 1 := by
  have hbaseNonneg : 0 ≤ hh18IterationScale * epsilon.1 :=
    mul_nonneg hh18IterationScale_pos.le hepsilon.le
  have hpower :
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) ≤ (1 / 2 : ℝ) := by
    calc
      (hh18IterationScale * epsilon.1) ^ (3 ^ depth) ≤
          (1 / 2 : ℝ) ^ (3 ^ depth) :=
        pow_le_pow_left₀ hbaseNonneg hsmall _
      _ ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (one_le_pow₀ (by norm_num : (1 : Nat) ≤ 3))
      _ = (1 / 2 : ℝ) := by norm_num
  have hscaled : hh18IterationScale *
      hh18DepthScheduleTargetError epsilon depth ≤ 1 / 2 := by
    rw [hh18CubicErrorEnvelope_closed_form]
    exact hpower
  have htargetPos := hh18DepthSchedule_targetError_pos epsilon hepsilon depth
  have htarget_le_scaled : hh18DepthScheduleTargetError epsilon depth ≤
      hh18IterationScale * hh18DepthScheduleTargetError epsilon depth := by
    nlinarith [hh18DepthScheduleScale_one_le]
  linarith
end QEC.Distillation.HH18Protocol
