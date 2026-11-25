-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:35.602779+00:00
-- url     : https://prove2.me/submissions/7f9fa868-5373-4968-b3e4-27c08ad3cf57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f

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
theorem _root_.solution (y x : Fin e → ℂ) :
    ∃ s : ℂ, hessForm B y x =
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by
  refine ⟨⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ, ?_⟩
  unfold hessForm
  rw [← norm_sq_toLp_mulVec, ← norm_sq_toLp_mulVec, ← chart_sub, ← chart_add]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
