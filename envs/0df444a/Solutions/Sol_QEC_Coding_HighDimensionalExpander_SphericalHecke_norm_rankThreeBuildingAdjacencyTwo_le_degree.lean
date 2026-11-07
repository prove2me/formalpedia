-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_rankThreeBuildingAdjacencyTwo_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:07.137776+00:00
-- url     : https://prove2.me/submissions/55d36546-3c95-4757-98da-c977a01e021a

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_two_inv


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    ‖rankThreeBuildingAdjacencyTwo k‖ ≤
      coloredAdjacencyDegree k 3 2 := by
  calc
    ‖rankThreeBuildingAdjacencyTwo k‖ ≤
        Real.sqrt ((coloredAdjacencyDegree k 3 2 : ℝ) *
          coloredAdjacencyDegree k 3 1) :=
      norm_buildingColoredAdjacencyOperatorOfInv_le k 3 2 1
        (fundamentalDoubleCoset_rankThree_two_inv k)
    _ = coloredAdjacencyDegree k 3 2 := by
      rw [coloredAdjacencyDegree_rankThree_one,
        coloredAdjacencyDegree_rankThree_two]
      rw [← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
