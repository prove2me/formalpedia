-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:13:10.300205+00:00
-- url     : https://prove2.me/submissions/a4b2aed7-b1a4-47a5-aca2-bf08ab2c2d96

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPhysicalInputCount_pos


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
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (depth : Nat) :
    Real.rpow ((codeDistance r w : ℝ) ^ depth)
        (routedDepthScheduleGamma w r m) =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by
  have hdistance : (1 : ℝ) < codeDistance r w := by
    exact_mod_cast codeDistance_two_le h
  have hratio : 0 <
      (physicalInputCount m w : ℝ) / logicalOutputCount m w := by
    apply div_pos
    · exact_mod_cast routedDepthPhysicalInputCount_pos h
    · exact_mod_cast routedDepthLogicalOutputCount_pos m w
  calc
    Real.rpow ((codeDistance r w : ℝ) ^ depth)
        (routedDepthScheduleGamma w r m) =
        Real.exp (Real.log ((codeDistance r w : ℝ) ^ depth) *
          routedDepthScheduleGamma w r m) := by
          exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) *
        Real.log ((physicalInputCount m w : ℝ) / logicalOutputCount m w)) := by
          unfold routedDepthScheduleGamma
          congr 1
          rw [Real.log_pow]
          field_simp [ne_of_gt (Real.log_pos hdistance)]
    _ = Real.rpow ((physicalInputCount m w : ℝ) / logicalOutputCount m w)
        (depth : ℝ) := by
          symm
          calc
            Real.rpow ((physicalInputCount m w : ℝ) / logicalOutputCount m w)
                (depth : ℝ) =
                Real.exp (Real.log ((physicalInputCount m w : ℝ) /
                  logicalOutputCount m w) * (depth : ℝ)) :=
              Real.rpow_def_of_pos hratio _
            _ = Real.exp ((depth : ℝ) *
                Real.log ((physicalInputCount m w : ℝ) /
                  logicalOutputCount m w)) :=
              congrArg Real.exp (mul_comm _ _)
    _ = ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth :=
      Real.rpow_natCast _ _
end QEC.Distillation.HH18Parameterized
