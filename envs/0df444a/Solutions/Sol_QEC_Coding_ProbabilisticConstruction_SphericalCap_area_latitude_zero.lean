-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_latitude_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:34.071809+00:00
-- url     : https://prove2.me/submissions/84a182f6-6ed4-4a5e-995d-49ff00d4a502

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_ambient_latitude_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_norm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    area {s : Sphere | inner ℝ (u : Space) (s : Space) = c} = 0 := by
  have hmeas : MeasurableSet {s : Sphere | inner ℝ (u : Space) (s : Space) = c} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [area,Measure.toSphere_apply' _ hmeas]
  have hsub : Ioo (0:ℝ) 1 • ((↑) '' {s : Sphere | inner ℝ (u : Space) (s : Space) = c}) ⊆
      {x : Space | c * ‖x‖ = inner ℝ (u : Space) x} := by
    rintro x ⟨r,hr,y,⟨s,hs,rfl⟩,rfl⟩
    change c * ‖r • (s : Space)‖ = inner ℝ (u : Space) (r • (s : Space))
    rw [displacement_norm r hr.1.le,real_inner_smul_right,hs,mul_comm]
  rw [measure_mono_null hsub (ambient_latitude_zero u c),mul_zero]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
