-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.sum_fundamentalHeckeFunction_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:18.26307+00:00
-- url     : https://prove2.me/submissions/3d3b1fda-7200-4c90-9cf9-eac5ca6c508d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_convolution_fundamentalHeckeFunction_apply_eq_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (n r s : ℕ)
    (a : HeckeGroup k (n + 1)) :
    (∑ q ∈ fundamentalNeighborCosets k (n + 1) r,
        fundamentalHeckeFunction k (n + 1) s (q.out⁻¹ * a)) =
      ∑ q ∈ fundamentalNeighborCosets k (n + 1) s,
        fundamentalHeckeFunction k (n + 1) r (q.out⁻¹ * a) := by
  rw [← convolution_fundamentalHeckeFunction_apply_eq_sum,
    ← convolution_fundamentalHeckeFunction_apply_eq_sum,
    mul_comm]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
