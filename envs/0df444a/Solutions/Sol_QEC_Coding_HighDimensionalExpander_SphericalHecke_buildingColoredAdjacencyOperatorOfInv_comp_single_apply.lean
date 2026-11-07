-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.buildingColoredAdjacencyOperatorOfInv_comp_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:24:57.623686+00:00
-- url     : https://prove2.me/submissions/104aeff4-ac38-49e8-8a32-78e1e577d1b3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_convolution_fundamentalHeckeFunction_apply_eq_sum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_sum_coloredBuildingNeighbors_eq_sum_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_buildingColoredAdjacencyOperatorOfInv_single_transported_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r r' s s' : ℕ)
    (hrset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d r')
    (hsset : (fundamentalDoubleCoset k d s)⁻¹ =
      fundamentalDoubleCoset k d s')
    (z x : BuildingVertex k d) :
    (buildingColoredAdjacencyOperatorOfInv k d r r' hrset ∘L
        buildingColoredAdjacencyOperatorOfInv k d s s' hsset)
        (buildingVertexDelta k d z) x =
      (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) (x.out⁻¹ * z.out) := by
  rw [ContinuousLinearMap.comp_apply,
    buildingColoredAdjacencyOperatorOfInv_apply_apply]
  rw [sum_coloredBuildingNeighbors_eq_sum_fundamental]
  simp_rw [buildingColoredAdjacencyOperatorOfInv_single_transported_apply
    k d r s s' hsset x z]
  calc
    (∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
        fundamentalHeckeFunction k d s
          (q.1.out⁻¹ * x.out⁻¹ * z.out)) =
        ∑ q ∈ fundamentalNeighborCosets k d r,
          fundamentalHeckeFunction k d s
            (q.out⁻¹ * (x.out⁻¹ * z.out)) := by
      rw [show (∑ q ∈ fundamentalNeighborCosets k d r,
          fundamentalHeckeFunction k d s
            (q.out⁻¹ * (x.out⁻¹ * z.out))) =
          ∑ q : {q // q ∈ fundamentalNeighborCosets k d r},
            fundamentalHeckeFunction k d s
              (q.1.out⁻¹ * (x.out⁻¹ * z.out)) by
        rw [← Finset.sum_attach, Finset.attach_eq_univ]]
      apply Fintype.sum_congr
      intro q
      rw [mul_assoc]
    _ = (fundamentalHeckeFunction k d r *
        fundamentalHeckeFunction k d s) (x.out⁻¹ * z.out) :=
      (convolution_fundamentalHeckeFunction_apply_eq_sum
        k d r s (x.out⁻¹ * z.out)).symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
