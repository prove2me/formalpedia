-- Prove2me | solution 1 for PositivityTheory.CW.nilpotent_of_power_traces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:28.81771+00:00
-- url     : https://prove2.me/submissions/2b4995db-b147-42c6-8de0-b3a6b3c6d975

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
import Theorems.Thm_PositivityTheory_CW_CharpolyPowerTraces_charpoly_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A4 := by
  unfold A4
  intro R _ _ n N h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hc := Matrix.aeval_self_charpoly N
  rw [CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow] at hc
  exact hc
end PositivityTheory.CW
