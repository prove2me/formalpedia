-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:25.244907+00:00
-- url     : https://prove2.me/submissions/85251637-ce1d-404e-b51a-0f7cc2d89b56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (a : ι → AlgebraicClosure ℚ) (ha : ∀ k, a k ≠ 0) :
    AlgebraicIndependent ℚ (fun k ↦ (C (a k) * X k : MvPolynomial ι (AlgebraicClosure ℚ))) := by
  let φ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k) * X k
  let ψ : MvPolynomial ι (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      MvPolynomial ι (AlgebraicClosure ℚ) := aeval fun k ↦ C (a k)⁻¹ * X k
  have hψφ : ψ.comp φ = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  have hφ : Function.Injective φ := Function.LeftInverse.injective (g := ψ) fun p ↦ by
    rw [← AlgHom.comp_apply, hψφ, AlgHom.id_apply]
  have h := ((MvPolynomial.algebraicIndependent_X ι (AlgebraicClosure ℚ)).map' hφ).restrictScalars
    (R := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  convert h using 1
  funext k
  simp [φ]
end GroundTheory.Heights₂.Heights.OrbitCurve
