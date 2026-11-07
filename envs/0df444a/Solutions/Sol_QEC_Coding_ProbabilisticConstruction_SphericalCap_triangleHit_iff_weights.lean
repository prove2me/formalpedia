-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.triangleHit_iff_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:30.462382+00:00
-- url     : https://prove2.me/submissions/f1188a04-95d3-48c7-82b2-1c40a5e5e851

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_convexHull_range_eq_barycenters
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
theorem _root_.solution (r : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (p : Fin 3 → Space) : p ∈ triangleHit r z ρ ↔
    ∃ w : stdSimplex ℝ (Fin 3), dist (∑ j, (w : Fin 3 → ℝ) j • (r j+p j)) z ≤ ρ := by
  simp only [triangleHit, mem_setOf_eq, convexHull_range_eq_barycenters, mem_image]
  constructor
  · rintro ⟨y,⟨w,hw,rfl⟩,h⟩
    exact ⟨⟨w,hw⟩,h⟩
  · rintro ⟨w,h⟩
    exact ⟨barycenterMap _ w, ⟨w,w.property,rfl⟩,h⟩
end QEC.Coding.ProbabilisticConstruction.SphericalCap
