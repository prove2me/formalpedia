-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.summable_inner_coloredBuildingEdge_target_source_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:53:09.531944+00:00
-- url     : https://prove2.me/submissions/c435b8f6-97ee-43d4-ad82-8740c257ff86

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
      fundamentalDoubleCoset k d s)
    (f g : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦
      inner ℂ (f e.2.1) (g e.1)) := by
  exact lp.summable_inner
      (coloredBuildingEdgeTargetL2OfInv k d r s hset f)
      (coloredBuildingEdgeSourceL2 k d r g)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
