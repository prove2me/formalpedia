-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_capSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:59.006917+00:00
-- url     : https://prove2.me/submissions/75bc4ed2-9b2f-4588-b7dc-655614be2a22

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capLaw_cap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_displacementCap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacementCap_preimage

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R c : ℝ} (hR : 0 < R) (u : Sphere) (hc : c < 1) :
    capDisplacementLaw R u c (displacementCap R u c) = 1 := by
  rw [capDisplacementLaw,Measure.map_apply (by fun_prop) (measurableSet_displacementCap R u c),
    displacementCap_preimage hR,capLaw_cap u hc]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
