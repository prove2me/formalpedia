-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_le_polylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:28:41.534845+00:00
-- url     : https://prove2.me/submissions/e0824866-9345-4f27-b71c-6d796a99f68f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_le_six_fifths
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleLogGrowthBase_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth))
          (routedDepthScheduleGamma w r m) := by
  have hbase : 0 < routedDepthScheduleLogGrowthBase w r m epsilon :=
    routedDepthScheduleLogGrowthBase_pos epsilon hepsilon hsmall
  have hbaseRpow : 0 <
      Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
        (routedDepthScheduleGamma w r m) :=
    Real.rpow_pos_of_pos hbase _
  have hlog := routedDepthSchedule_distancePow_mul_logGrowthBase_eq_log
    (w := w) (r := r) (m := m) epsilon hepsilon depth
  have hfactorization :
      Real.rpow ((codeDistance r w : ℝ) ^ depth *
          routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) =
        Real.rpow ((codeDistance r w : ℝ) ^ depth)
          (routedDepthScheduleGamma w r m) *
        Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) :=
    Real.mul_rpow (by positivity) hbase.le
  calc
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
        (6 / 5 : ℝ) *
          ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
      routedDepthScheduleSuccessfulOutputCost_le_six_fifths h hdegree epsilon
        hsmall depth
    _ = (6 / 5 : ℝ) *
        Real.rpow ((codeDistance r w : ℝ) ^ depth)
          (routedDepthScheduleGamma w r m) := by
      rw [routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow h depth]
    _ =
        ((6 / 5 : ℝ) *
          Real.rpow ((codeDistance r w : ℝ) ^ depth)
            (routedDepthScheduleGamma w r m) *
          Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
            (routedDepthScheduleGamma w r m)) /
          Real.rpow (routedDepthScheduleLogGrowthBase w r m epsilon)
            (routedDepthScheduleGamma w r m) := by
      field_simp [ne_of_gt hbaseRpow]
    _ = routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow ((codeDistance r w : ℝ) ^ depth *
          routedDepthScheduleLogGrowthBase w r m epsilon)
          (routedDepthScheduleGamma w r m) := by
      rw [hfactorization]
      unfold routedDepthScheduleCostCoefficient
      field_simp [ne_of_gt hbaseRpow]
    _ = routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth))
          (routedDepthScheduleGamma w r m) := by
      rw [hlog]
end QEC.Distillation.HH18Parameterized
