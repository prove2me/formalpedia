-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.adjoint_buildingColoredAdjacencyOperatorOfInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:46.475844+00:00
-- url     : https://prove2.me/submissions/5b8abf17-2c0e-40fa-9380-0ca2f2f181c7

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_inner_buildingColoredAdjacencyOperatorOfInv

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
      fundamentalDoubleCoset k d s)
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d r) :
    (buildingColoredAdjacencyOperatorOfInv k d r s hset)† =
      buildingColoredAdjacencyOperatorOfInv k d s r hsset := by
  rw [← eq_comm]
  exact (ContinuousLinearMap.eq_adjoint_iff
    (buildingColoredAdjacencyOperatorOfInv k d s r hsset)
    (buildingColoredAdjacencyOperatorOfInv k d r s hset)).2
      (fun f g ↦ inner_buildingColoredAdjacencyOperatorOfInv
        k d s r hsset hset f g)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
