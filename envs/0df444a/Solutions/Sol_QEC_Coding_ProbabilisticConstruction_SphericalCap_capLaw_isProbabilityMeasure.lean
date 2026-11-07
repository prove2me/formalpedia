-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:38.827326+00:00
-- url     : https://prove2.me/submissions/aab46192-81c1-469a-a50c-0563780a9d45

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_ne_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_ne_top
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {c : ℝ} (hc : c < 1) :
    IsProbabilityMeasure (capLaw u c) := by
  constructor
  simp only [capLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (area_cap_ne_zero u hc) (area_cap_ne_top u c)
end QEC.Coding.ProbabilisticConstruction.SphericalCap
