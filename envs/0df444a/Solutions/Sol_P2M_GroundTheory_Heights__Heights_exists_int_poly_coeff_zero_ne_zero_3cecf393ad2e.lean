-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_int_poly_coeff_zero_ne_zero_3cecf393ad2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:53.870841+00:00
-- url     : https://prove2.me/submissions/d4e2a1d2-7b14-4620-a754-3de754698905

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDivVertical

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {τ : AlgebraicClosure ℚ} (hτ : τ ≠ 0) :
    ∃ P : Polynomial ℤ, P.coeff 0 ≠ 0 ∧ Polynomial.aeval τ P = 0 := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  obtain ⟨Q, hQ, hQτ⟩ :=
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic τ⁻¹).restrictScalars (R := ℤ)
  have : Invertible τ⁻¹ := invertibleOfNonzero (inv_ne_zero hτ)
  refine ⟨Q.reverse, by rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ, ?_⟩
  have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)) τ⁻¹ Q).mpr hQτ
  rwa [invOf_eq_inv, inv_inv] at h
end GroundTheory.Heights₂.Heights
