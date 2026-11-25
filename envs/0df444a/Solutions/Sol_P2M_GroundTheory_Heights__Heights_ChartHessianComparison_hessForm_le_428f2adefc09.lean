-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:04.20666+00:00
-- url     : https://prove2.me/submissions/739f6174-ced7-40c6-af81-28c4fab77ffd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_ne_zero_9391c43103f6

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
theorem _root_.solution (hB : B.det ≠ 0) (y x : Fin e → ℂ) (s : ℂ) :
    hessForm B y x ≤
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by
  have hu := chart_ne_zero B hB y
  unfold hessForm
  rw [← norm_sq_toLp_mulVec, ← norm_sq_toLp_mulVec, ← chart_sub, ← chart_add]
  exact div_le_div_of_nonneg_right (norm_sub_proj_le _ _ hu s) (by positivity)
end GroundTheory.Heights₂.Heights.ChartHessianComparison
