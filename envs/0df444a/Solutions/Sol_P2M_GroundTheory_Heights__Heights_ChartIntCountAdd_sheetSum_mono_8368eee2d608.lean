-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:32.26111+00:00
-- url     : https://prove2.me/submissions/2161e1bd-e62f-430e-99ff-5e5da4b98247

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_eq_sum_033c841426d6

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntCountAdd
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hFG x _
  · simp only [dif_neg h, le_refl]
end GroundTheory.Heights₂.Heights.ChartIntCountAdd
