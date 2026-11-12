-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:47:31.397544+00:00
-- url     : https://prove2.me/submissions/de960b8b-e935-42b5-83f4-787dee4f4d47

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleGamma_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleLogGrowthBase_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_threePow_mul_logGrowthBase_le_log
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleSuccessfulOutputCost_le_two_rpow

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
    DependentBatch.typedSuccessfulOutputCost
      (hh18DepthScheduleInputSlots depth)
      (hh18DepthScheduleOutputSlots depth)
      (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        hh18DepthScheduleCostCoefficient epsilon *
          Real.rpow
            (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
            hh18DepthScheduleGamma := by
  have hbasePos : 0 < hh18DepthScheduleLogGrowthBase epsilon :=
    hh18DepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall
  have hexponentPos : 0 < hh18DepthScheduleGamma :=
    hh18DepthScheduleGamma_pos
  have hlog :
      (3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon ≤
        Real.log (1 / hh18DepthScheduleTargetError epsilon depth) :=
    hh18DepthSchedule_threePow_mul_logGrowthBase_le_log epsilon hepsilon
      depth
  have hpowComparison :
      Real.rpow ((3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon)
          hh18DepthScheduleGamma ≤
        Real.rpow (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma :=
    Real.rpow_le_rpow
      (mul_nonneg (by positivity) hbasePos.le) hlog hexponentPos.le
  have hfactorization :
      Real.rpow ((3 : ℝ) ^ depth * hh18DepthScheduleLogGrowthBase epsilon)
          hh18DepthScheduleGamma =
        Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma :=
    Real.mul_rpow (by positivity) hbasePos.le
  have hbaseRpowPos :
      0 < Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
        hh18DepthScheduleGamma :=
    Real.rpow_pos_of_pos hbasePos _
  rw [hfactorization] at hpowComparison
  have htwiceComparison :
      2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma ≤
        2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma := by
    calc
      2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma =
          2 * (Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
            Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
              hh18DepthScheduleGamma) := by ring
      _ ≤ 2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma :=
        mul_le_mul_of_nonneg_left hpowComparison (by norm_num)
  calc
    DependentBatch.typedSuccessfulOutputCost
        (hh18DepthScheduleInputSlots depth)
        (hh18DepthScheduleOutputSlots depth)
        (hh18DepthScheduleYieldFactor epsilon hsmall depth) ≤
        2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma :=
      hh18DepthScheduleSuccessfulOutputCost_le_two_rpow epsilon hsmall depth
    _ =
        (2 * Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma *
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma) /
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma := by
      field_simp [ne_of_gt hbaseRpowPos]
    _ ≤
        (2 * Real.rpow
          (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
          hh18DepthScheduleGamma) /
          Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
            hh18DepthScheduleGamma :=
      div_le_div_of_nonneg_right htwiceComparison hbaseRpowPos.le
    _ = hh18DepthScheduleCostCoefficient epsilon *
          Real.rpow
            (Real.log (1 / hh18DepthScheduleTargetError epsilon depth))
            hh18DepthScheduleGamma := by
      unfold hh18DepthScheduleCostCoefficient
      field_simp [ne_of_gt hbaseRpowPos]
end QEC.Distillation.HH18Protocol
