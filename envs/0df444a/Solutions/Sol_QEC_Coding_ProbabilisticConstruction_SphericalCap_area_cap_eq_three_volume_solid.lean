-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_eq_three_volume_solid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:23.571721+00:00
-- url     : https://prove2.me/submissions/39fb16d9-4519-4eae-9ebe-9ee6c56c318f

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_openCone_subset_solid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_mem_openCone_of_mem_solid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    area (cap u c) = 3 * (volume : Measure Space) (solidCapCone u c) := by
  rw [area, Measure.toSphere_apply' _ (measurableSet_cap u c)]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd]
  congr 1
  apply measure_eq_measure_of_null_diff (openCone_subset_solid u c)
  have hsub : solidCapCone u c \ (Ioo (0 : ℝ) 1 • ((↑) '' cap u c)) ⊆
      sphere (0 : Space) 1 ∪ {0} := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inr h0
    · left
      have h1 : ‖x‖ = 1 := by
        by_contra h1
        exact hx.2 (mem_openCone_of_mem_solid u c hx.1 h0 h1)
      simpa only [mem_sphere, dist_zero_right] using h1
  apply measure_mono_null hsub
  exact measure_union_null (Measure.addHaar_sphere volume 0 1) (measure_singleton 0)
end QEC.Coding.ProbabilisticConstruction.SphericalCap
