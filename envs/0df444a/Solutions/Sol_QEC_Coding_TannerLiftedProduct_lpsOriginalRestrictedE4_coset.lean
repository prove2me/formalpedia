-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRestrictedE4_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:31:30.234263+00:00
-- url     : https://prove2.me/submissions/3a010e46-7f4d-4b65-a39c-04a3fb6048b2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4CubePower_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N k : ℕ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc
      (lpsOriginalMeromorphicE4PowerAtLevel N k) q τ =
      (ModularForm.E₄ τ^3)^k := by
  induction q using Quotient.inductionOn with
  | h g =>
    let D : ModularForm 𝒮ℒ ((k : ℤ)*12) :=
      (lpsOriginalE4CubePower k).mcast (by ring)
    change ((D : ℍ → ℂ) ∣[(k : ℤ)*12] g.val⁻¹) τ = _
    rw [SlashInvariantForm.slash_action_eqn D g.val⁻¹ (inv_mem g.property)]
    exact lpsOriginalE4CubePower_apply k τ
end QEC.Coding.TannerLiftedProduct
