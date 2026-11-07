-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:07.250406+00:00
-- url     : https://prove2.me/submissions/1af4d2d6-f040-44b7-92d6-76771d4acfad

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution : area univ = ENNReal.ofReal (4 * Real.pi) := by
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [area,Measure.toSphere_apply_univ,hd,EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one,one_pow,one_mul]
  norm_num only
  have he : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
