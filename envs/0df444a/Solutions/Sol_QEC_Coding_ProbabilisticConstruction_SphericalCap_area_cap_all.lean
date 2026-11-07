-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:28.564083+00:00
-- url     : https://prove2.me/submissions/ce482567-b33a-4d27-a488-8f8dc87364ce

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_height_mem_Icc
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_latitude_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_univ
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    area (cap u c) = ENNReal.ofReal (2 * Real.pi * capHeight c) := by
  by_cases hlow : c ≤ -1
  · have he : cap u c = univ := by
      ext s
      simp only [cap,mem_setOf_eq,mem_univ,iff_true]
      exact hlow.trans (height_mem_Icc u s).1
    rw [he,area_univ]
    congr 1
    simp [capHeight,max_eq_left hlow] <;> ring
  · by_cases hhigh : 1 ≤ c
    · have hs : cap u c ⊆ {s : Sphere | inner ℝ (u : Space) (s : Space) = 1} := by
        intro s h
        exact le_antisymm (height_mem_Icc u s).2 (hhigh.trans h)
      rw [measure_mono_null hs (area_latitude_zero u 1)]
      have hh : capHeight c = 0 := by
        simp only [capHeight,max_eq_right (by linarith : (-1:ℝ) ≤ c),
          max_eq_left (by linarith : 1-c ≤ 0)]
      simp [hh]
    · have hc0 : -1 < c := lt_of_not_ge hlow
      have hc1 : c < 1 := lt_of_not_ge hhigh
      rw [area_cap u hc0 hc1]
      simp only [capHeight,max_eq_right hc0.le,max_eq_right (by linarith : 0 ≤ 1-c)]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
