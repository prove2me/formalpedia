-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:25.023855+00:00
-- url     : https://prove2.me/submissions/8dcaa908-8ade-405a-9128-44c08d24cab7

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
    (hfin : (fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h, abs_zero, le_refl]
end GroundTheory.Heights₂.Heights.ChartIntCountAdd
