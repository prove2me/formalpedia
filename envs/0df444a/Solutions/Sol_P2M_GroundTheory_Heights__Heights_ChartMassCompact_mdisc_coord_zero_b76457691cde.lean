-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:26.082545+00:00
-- url     : https://prove2.me/submissions/d04a9bf3-307e-4e0a-853f-6b90086565dc

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_polCoef
import Theorems.Thm_ReciprocityTheory_AnForm_A_polCoef_eq_zero


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
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMassCompact
theorem _root_.solution {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by
  rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨j, hj⟩ := hr i
    refine mul_eq_zero_of_right _ (Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_)
    simp [hj, hi]
  · rw [ReciprocityTheory.AnForm.A.polCoef_eq_zero r hr, zero_mul]
end GroundTheory.Heights₂.Heights.ChartMassCompact
