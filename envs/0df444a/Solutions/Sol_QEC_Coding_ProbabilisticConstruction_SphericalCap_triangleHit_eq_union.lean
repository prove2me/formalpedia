-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:47.826062+00:00
-- url     : https://prove2.me/submissions/8ddf36d9-584d-495f-bf90-c3b997220627

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_iff_weights
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_large_weight
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleHit r z ρ = ⋃ i, largeWeightHit r z ρ i := by
  ext p
  rw [triangleHit_iff_weights]
  simp only [mem_iUnion,largeWeightHit,mem_setOf_eq]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨i,hi⟩ := exists_large_weight w.property
    exact ⟨i,w,hi,hw⟩
  · rintro ⟨i,w,_,hw⟩
    exact ⟨w,hw⟩
end QEC.Coding.ProbabilisticConstruction.SphericalCap
