-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_nullSingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:56.962195+00:00
-- url     : https://prove2.me/submissions/3fbfab18-7692-4aeb-a88a-1a1d75a657f1

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacement_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R : ℝ} (hR : R ≠ 0) (u : Sphere) (c : ℝ) :
    MeasureTheory.NullSingletonClass (capDisplacementLaw R u c) := by
  constructor
  intro p
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton p)]
  have hs : ((fun s : Sphere => R • (s : Space)) ⁻¹' ({p} : Set Space)).Subsingleton := by
    intro s hs t ht
    apply displacement_injective hR
    exact hs.trans ht.symm
  exact hs.measure_zero _
end QEC.Coding.ProbabilisticConstruction.SphericalCap
