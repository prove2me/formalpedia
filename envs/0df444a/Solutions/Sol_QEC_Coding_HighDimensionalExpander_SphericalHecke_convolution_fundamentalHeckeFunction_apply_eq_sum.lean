-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.convolution_fundamentalHeckeFunction_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:57.76258+00:00
-- url     : https://prove2.me/submissions/c76370b3-5577-4f05-a587-63f8f91a4289

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_coloredAdjacency_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (a : HeckeGroup k d) :
    (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) a =
      ∑ q ∈ fundamentalNeighborCosets k d r,
        fundamentalHeckeFunction k d s (q.out⁻¹ * a) := by
  rw [show (fundamentalHeckeFunction k d r *
      fundamentalHeckeFunction k d s) a =
      ∫ t in fundamentalDoubleCoset k d r,
        fundamentalHeckeFunction k d s (t⁻¹ * a)
          ∂normalizedLocalHaarMeasure k d by
    exact coloredAdjacency_apply k d r
      (fundamentalHeckeFunction k d s) a]
  exact setIntegral_fundamentalDoubleCoset_eq_sum_neighbors k d r
    (fun t ↦ fundamentalHeckeFunction k d s (t⁻¹ * a))
    ((fundamentalHeckeFunction k d s).continuous.comp
      (continuous_inv.mul continuous_const))
    (by
      intro g q hq
      change fundamentalHeckeFunction k d s ((g * q)⁻¹ * a) =
        fundamentalHeckeFunction k d s (g⁻¹ * a)
      rw [mul_inv_rev, mul_assoc]
      exact (fundamentalHeckeFunction k d s).left_invariant q⁻¹
        ((maximalCompact k d).inv_mem hq) (g⁻¹ * a))
end QEC.Coding.HighDimensionalExpander.SphericalHecke
