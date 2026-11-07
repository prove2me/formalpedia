-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenter_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:46.382867+00:00
-- url     : https://prove2.me/submissions/bee7bf96-8e4f-4ebf-a4f0-9ba8575de45e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3)) :
    (∑ j, (w : Fin 3 → ℝ) j • a j)-z =
      ∑ j, (w : Fin 3 → ℝ) j • (a j-z) := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  erw [w.property.2]
  rw [one_smul]
end QEC.Coding.ProbabilisticConstruction.SphericalCap
