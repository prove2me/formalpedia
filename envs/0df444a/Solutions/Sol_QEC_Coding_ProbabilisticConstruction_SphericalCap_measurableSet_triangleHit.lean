-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_triangleHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:41:49.591148+00:00
-- url     : https://prove2.me/submissions/2e713e94-811c-4282-8b7f-bf79212adb37

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_largeWeightHit
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_triangleHit_eq_union

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (r : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    MeasurableSet (triangleHit r z ρ) := by
  rw [triangleHit_eq_union]
  exact MeasurableSet.iUnion fun i => (isClosed_largeWeightHit r z ρ i).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
