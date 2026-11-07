-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.ambient_latitude_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:35.652161+00:00
-- url     : https://prove2.me/submissions/ae440c18-75ae-46a2-9db7-bc693f0a00b0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axial_level_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axisReflection_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axisReflection_measurePreserving
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    (volume : Measure Space) {x | c * ‖x‖ = inner ℝ (u : Space) x} = 0 := by
  have he : {x : Space | c * ‖x‖ = inner ℝ (u : Space) x} =
      axisReflection (u : Space) (north : Space) ⁻¹' {x : Space | c * ‖x‖ = x 0} := by
    ext x
    have hu : axisReflection (u : Space) (north : Space) (u : Space) = (north : Space) :=
      axisReflection_apply _ _ (by simp)
    have hi := (axisReflection (u : Space) (north : Space)).inner_map_map (u : Space) x
    rw [hu] at hi
    have hcoord : inner ℝ (north : Space) (axisReflection (u : Space) (north : Space) x) =
        (axisReflection (u : Space) (north : Space) x) 0 := by
      simp only [north,EuclideanSpace.basisFun_inner]
    rw [hcoord] at hi
    simp only [mem_setOf_eq,mem_preimage,LinearIsometryEquiv.norm_map,hi]
  rw [he, (axisReflection_measurePreserving (u : Space) (north : Space)).measure_preimage]
  · exact axial_level_zero c
  · exact (isClosed_eq (continuous_const.mul continuous_norm)
      (by fun_prop)).measurableSet.nullMeasurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
