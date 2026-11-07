-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankThreeBuildingAdjacencyOne_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:06.045554+00:00
-- url     : https://prove2.me/submissions/9e5e0b36-0107-4f44-9669-b732920eee87

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_norm_buildingColoredAdjacencyOperatorOfInv_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coloredAdjacencyDegree_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_one_inv


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    ‖rankThreeBuildingAdjacencyOne k‖ ≤
      coloredAdjacencyDegree k 3 1 := by
  calc
    ‖rankThreeBuildingAdjacencyOne k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 3 1 : ℝ) *
          coloredAdjacencyDegree k 3 2) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 3 1 2
        (fundamentalDoubleCoset_rankThree_one_inv k)
    _ = coloredAdjacencyDegree k 3 1 := by
      rw [coloredAdjacencyDegree_rankThree_one,
        coloredAdjacencyDegree_rankThree_two]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
