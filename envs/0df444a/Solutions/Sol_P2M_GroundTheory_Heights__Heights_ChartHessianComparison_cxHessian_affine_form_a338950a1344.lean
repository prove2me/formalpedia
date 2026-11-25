-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:45.305743+00:00
-- url     : https://prove2.me/submissions/8f912adc-cd34-4b37-9f40-3b4f270f5ffa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_form_80017e7b56b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gram_numer_eq_332c7ad174d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y x : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    star x ⬝ᵥ (cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y *ᵥ x) =
      ((‖L (star x) - (⟪c + L y, L (star x)⟫_ℂ / ⟪c + L y, c + L y⟫_ℂ) • (c + L y)‖ ^ 2 /
        (2 * ‖c + L y‖ ^ 2) : ℝ) : ℂ) := by
  have hD : ∑ i, star (x i) • L (Pi.single i 1) = L (star x) := by
    simp_rw [← L.map_smul, ← map_sum]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [cxHessian_affine c L y h0, gramHess_form, hD, gram_numer_eq _ _ h0]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
