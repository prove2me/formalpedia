-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cos_mem_open_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:07:53.270453+00:00
-- url     : https://prove2.me/submissions/eccdc4fd-d8bd-4e81-8e4d-bd243e65e8d8

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
theorem _root_.solution {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    -1 < Real.cos θ ∧ Real.cos θ < 1 := by
  constructor
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
end QEC.Coding.ProbabilisticConstruction.SphericalCap
