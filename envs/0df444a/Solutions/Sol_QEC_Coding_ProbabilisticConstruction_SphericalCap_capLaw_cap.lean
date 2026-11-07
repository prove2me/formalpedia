-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capLaw_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:19.912342+00:00
-- url     : https://prove2.me/submissions/b06503bb-ba94-42d0-8252-4c37b185528c

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_cap
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
theorem _root_.solution (u : Sphere) {c : ℝ} (hc : c < 1) : capLaw u c (cap u c) = 1 := by
  simp only [capLaw, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_cap u c), inter_self, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (area_cap_ne_zero u hc) (area_cap_ne_top u c)
end QEC.Coding.ProbabilisticConstruction.SphericalCap
