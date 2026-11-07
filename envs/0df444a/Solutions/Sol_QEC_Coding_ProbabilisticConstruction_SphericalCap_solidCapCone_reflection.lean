-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_reflection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:29.193412+00:00
-- url     : https://prove2.me/submissions/c59a1d1e-a92a-4275-aab6-92c0d9bdd9f2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axisReflection_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u v : Sphere) (c : ℝ) :
    solidCapCone u c = axisReflection (u : Space) (v : Space) ⁻¹' solidCapCone v c := by
  ext x
  have hu : axisReflection (u : Space) (v : Space) (u : Space) = (v : Space) :=
    axisReflection_apply _ _ (by simp)
  have hi := (axisReflection (u : Space) (v : Space)).inner_map_map (u : Space) x
  rw [hu] at hi
  simp only [solidCapCone, mem_setOf_eq, mem_preimage,
    LinearIsometryEquiv.norm_map, hi]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
