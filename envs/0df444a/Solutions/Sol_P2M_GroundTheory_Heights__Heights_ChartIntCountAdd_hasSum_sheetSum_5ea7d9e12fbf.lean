-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:28.869694+00:00
-- url     : https://prove2.me/submissions/c53cf203-30d4-48d7-8629-1a7df4cf62ad

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
    (hfin : (fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by
  classical
  simp only [sheetSum_eq_sum hfin]
  refine hasSum_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hF x _
  · simp only [dif_neg h]; exact hasSum_zero
end GroundTheory.Heights₂.Heights.ChartIntCountAdd
