-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_except
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:48.737738+00:00
-- url     : https://prove2.me/submissions/746b6b42-2605-43a9-9c1d-b2d88a9b8083

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_exists_unit_normal_pair
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
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
theorem _root_.solution (a : Fin 3 → Space) (z : Space) (i : Fin 3) :
    ∃ n : Sphere, ∀ j, j ≠ i → inner ℝ (n : Space) (a j-z) = 0 := by
  obtain ⟨n,hn,h0,h1⟩ := exists_unit_normal_pair (a (i.succAbove 0)-z) (a (i.succAbove 1)-z)
  refine ⟨⟨n, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩, ?_⟩
  intro j hj
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
  fin_cases k
  · exact h0
  · exact h1
end QEC.Coding.ProbabilisticConstruction.SphericalCap
