-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:57.999206+00:00
-- url     : https://prove2.me/submissions/d358ced0-8d03-41ec-903d-0ead83a2e2aa

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_isProbabilityMeasure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_norm
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R : ℝ} (hR : 0 ≤ R) (u : Sphere) {c : ℝ}
    (hc : c < 1) : capDisplacementLaw R u c (sphere (0 : Space) R) = 1 := by
  letI := capLaw_isProbabilityMeasure u hc
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
  have he : (fun s : Sphere => R • (s : Space)) ⁻¹' sphere (0 : Space) R = univ := by
    ext s
    simp only [mem_preimage, mem_sphere, dist_zero_right, displacement_norm R hR,
      mem_univ, iff_true]
  rw [he, measure_univ]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
