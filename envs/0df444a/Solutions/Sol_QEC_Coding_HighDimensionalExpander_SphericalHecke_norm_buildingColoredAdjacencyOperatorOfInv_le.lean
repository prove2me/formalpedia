-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.norm_buildingColoredAdjacencyOperatorOfInv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:34:37.680845+00:00
-- url     : https://prove2.me/submissions/9c6abdec-d2db-437c-9e27-ef489a059a29

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    ‖buildingColoredAdjacencyOperatorOfInv k d r s hset‖ ≤
      Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
        coloredAdjacencyDegree k d s) := by
  exact (buildingColoredAdjacencyLinearMapOfInv k d r s hset).mkContinuous_norm_le
    (Real.sqrt_nonneg _)
    (norm_buildingColoredAdjacencyLinearMapOfInv_le k d r s hset)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
