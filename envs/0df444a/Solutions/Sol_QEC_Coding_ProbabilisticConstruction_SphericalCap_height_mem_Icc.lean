-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.height_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:51.865867+00:00
-- url     : https://prove2.me/submissions/59d6b1d4-4c15-4476-b04a-719d1d920551

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u s : Sphere) : inner ℝ (u : Space) (s : Space) ∈ Icc (-1:ℝ) 1 := by
  have h := abs_real_inner_le_norm (u : Space) (s : Space)
  simpa only [norm_coe,mul_one,abs_le,mem_Icc] using h
end QEC.Coding.ProbabilisticConstruction.SphericalCap
