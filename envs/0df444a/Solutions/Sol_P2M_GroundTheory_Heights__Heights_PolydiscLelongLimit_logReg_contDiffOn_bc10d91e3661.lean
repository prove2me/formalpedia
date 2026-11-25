-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PolydiscLelongLimit_logReg_contDiffOn_bc10d91e3661
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:21.846561+00:00
-- url     : https://prove2.me/submissions/e594c342-88c4-4119-a75d-284e7a043d8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ProjectiveLineZeroFormHolds
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolydiscLelongLimit
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.PolydiscLelongLimit
namespace GroundTheory.Heights₂.Heights.PolydiscLelongLimit
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt
end GroundTheory.Heights₂.Heights.PolydiscLelongLimit
