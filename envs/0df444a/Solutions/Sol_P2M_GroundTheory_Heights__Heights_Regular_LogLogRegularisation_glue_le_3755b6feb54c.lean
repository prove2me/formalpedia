-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogLogRegularisation_glue_le_3755b6feb54c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:24.320718+00:00
-- url     : https://prove2.me/submissions/1414b57c-73c2-478c-ae50-996783110abd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le


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
open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
open Classical
namespace GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
theorem _root_.solution (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε c : ℝ} (hε : 0 ≤ ε) {x : X}
    (h : ∀ j, x ∈ P.mid j → a j x ≤ c) : P.glue a ε x ≤ c + ε := by
  unfold PotentialCharts.glue
  have h1 := regMax_le hε (fun i : {i // x ∈ P.mid i} => a i x)
  have h2 : tmax (fun i : {i // x ∈ P.mid i} => a i x) ≤ c := tmax_le fun i => h i.1 i.2
  linarith
end GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation
