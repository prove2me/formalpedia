-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_algebraicIndependent_C_mul_X_edadd42bd2c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:17.115086+00:00
-- url     : https://prove2.me/submissions/7f88ee8f-d00b-4aac-9c06-86d9f1babf00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution (a : K → Ω) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent Ω (fun k ↦ (C (a k) * X k : MvPolynomial K Ω)) := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k ↦ C (a k) * X k
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k ↦ C (a k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  have hφ : Function.Injective φ := Function.LeftInverse.injective (g := ψ) fun p ↦ by
    rw [← AlgHom.comp_apply, hψφ, AlgHom.id_apply]
  convert (MvPolynomial.algebraicIndependent_X K Ω).map' hφ using 1
  funext k
  simp [φ]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
