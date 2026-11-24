-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:48.03312+00:00
-- url     : https://prove2.me/submissions/004797a7-f1b4-46cf-a4e4-f3bab030fdce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20

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
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (v : Fin (e + 1) → ℂ) :
    ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1)))‖ ^ 2 = (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re := by
  rw [← inner_toLp_mulVec]
  have h : ⟪(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))), WithLp.toLp 2 (B *ᵥ v)⟫_ℂ =
      ((‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1)))‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
