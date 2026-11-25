-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.radialBump_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:34.859391+00:00
-- url     : https://prove2.me/submissions/ed886d5d-7e9e-407f-a9a9-243c19e6438b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshMol
theorem _root_.solution (D : ℕ) : HasCompactSupport (g0 D) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun w hw => by
    by_contra h
    exact hw (ball_subset_closedBall (radialBump_support D h))
end ReciprocityTheory.AnForm.A.PshMol
