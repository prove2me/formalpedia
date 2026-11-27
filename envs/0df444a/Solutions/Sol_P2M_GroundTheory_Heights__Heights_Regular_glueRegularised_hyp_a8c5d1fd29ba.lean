-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_glueRegularised_hyp_a8c5d1fd29ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:44.683559+00:00
-- url     : https://prove2.me/submissions/938e79b4-c06f-4247-8b84-8fc6c9c89917

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_pointCutoff_d7eee880fa4e
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollifierInhabit_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution : ∃ ρ : Mollifier 0,
    pointReg.IsCutoffFamily (fun _ _ => 0) 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
    (∀ j, ∀ x ∈ closure (pointReg.mid j), closedBall (pointReg.chart j x) 1 ⊆ (pointReg.chart j).target) ∧
    (∀ j k, ∀ x ∈ pointReg.mid j ∩ pointReg.mid k,
      |pointReg.phReg ρ 0 1 j x - pointReg.phReg ρ 0 1 k x| ≤ 1) := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm 0
  refine ⟨ρ, pointCutoff, by norm_num, by norm_num, fun _ _ _ y _ => ?_, fun j k _ _ => ?_⟩
  · simp [pointReg, pointCharts, pointChart]
  · obtain rfl : j = k := Subsingleton.elim (α := Fin 1) j k
    simp
end GroundTheory.Heights₂.Heights.Regular
