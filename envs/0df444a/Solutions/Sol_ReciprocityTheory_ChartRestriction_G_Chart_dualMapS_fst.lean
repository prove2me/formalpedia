-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:04.711841+00:00
-- url     : https://prove2.me/submissions/fa9430ad-f431-4fbe-87f2-2f06402d2c26

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
    (x : DualNumber A) : (dualMapS ι x).fst = ι x.fst := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
end ReciprocityTheory.ChartRestriction.G.Chart
