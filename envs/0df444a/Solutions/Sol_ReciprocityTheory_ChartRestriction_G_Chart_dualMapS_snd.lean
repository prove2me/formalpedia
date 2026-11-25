-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:10.766883+00:00
-- url     : https://prove2.me/submissions/437fdb57-3fee-42b2-8aca-d284104d91be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Theorems.Thm_Bl_FirstBlockLemmaK_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).snd = ι x.snd := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
end ReciprocityTheory.ChartRestriction.G.Chart
