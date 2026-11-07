-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.setIntegral_fundamentalDoubleCoset_eq_sum_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:54:28.796306+00:00
-- url     : https://prove2.me/submissions/6cf9a021-38ed-462a-a4cf-daaa4465952e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_quotientFiber_isCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_eq_biUnion_quotientFiber
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_quotientFiber_eq_preimage_left_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (F : HeckeGroup k d → ℂ) (hF : Continuous F)
    (hK : ∀ g q : HeckeGroup k d, q ∈ maximalCompact k d →
      F (g * q) = F g) :
    ∫ x in fundamentalDoubleCoset k d r, F x
        ∂normalizedLocalHaarMeasure k d =
      ∑ q ∈ fundamentalNeighborCosets k d r, F q.out := by
  rw [fundamentalDoubleCoset_eq_biUnion_quotientFiber]
  rw [integral_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro q hq
    let μ := normalizedLocalHaarMeasure k d
    let fiber : Set (HeckeGroup k d) :=
      (QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {q}
    have hfiber : MeasurableSet fiber := by
      dsimp only [fiber]
      rw [quotientFiber_eq_preimage_left_mul]
      exact (maximalCompact_isOpen k d).measurableSet.preimage
        (measurable_const_mul q.out⁻¹)
    have hpointwise :
        (fun x => fiber.indicator F (q.out * x)) =
          (fun x => (maximalCompact k d : Set (HeckeGroup k d)).indicator
            (fun _ => F q.out) x) := by
      funext x
      have hmem : q.out * x ∈ fiber ↔ x ∈ maximalCompact k d := by
        dsimp only [fiber]
        rw [quotientFiber_eq_preimage_left_mul]
        simp
      by_cases hx : x ∈ maximalCompact k d
      · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx,
          hK q.out x hx]
      · rw [Set.indicator_of_notMem (not_congr hmem |>.mpr hx),
          Set.indicator_of_notMem hx]
    calc
      ∫ x in fiber, F x ∂μ = ∫ x, fiber.indicator F x ∂μ := by
        rw [integral_indicator hfiber]
      _ = ∫ x, fiber.indicator F (q.out * x) ∂μ :=
        (integral_mul_left_eq_self (fiber.indicator F) q.out).symm
      _ = ∫ x, (maximalCompact k d : Set (HeckeGroup k d)).indicator
          (fun _ => F q.out) x ∂μ := by rw [hpointwise]
      _ = ∫ x in (maximalCompact k d : Set (HeckeGroup k d)),
          F q.out ∂μ := by
        rw [integral_indicator (maximalCompact_isOpen k d).measurableSet]
      _ = F q.out := by
        rw [setIntegral_const]
        change (normalizedLocalHaarMeasure k d).real
            (maximalCompact k d : Set (HeckeGroup k d)) • F q.out = F q.out
        rw [Measure.real, normalizedLocalHaarMeasure_maximalCompact,
          ENNReal.toReal_one, one_smul]
  · intro q hq
    rw [quotientFiber_eq_preimage_left_mul]
    exact (maximalCompact_isOpen k d).measurableSet.preimage
      (measurable_const_mul q.out⁻¹)
  · intro a ha b hb hab
    change Disjoint
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {a})
      ((QuotientGroup.mk : HeckeGroup k d → BuildingVertex k d) ⁻¹' {b})
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  · intro q hq
    exact hF.continuousOn.integrableOn_compact
      (quotientFiber_isCompact k d q)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
