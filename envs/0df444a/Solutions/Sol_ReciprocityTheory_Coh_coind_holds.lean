-- Prove2me | solution 1 for ReciprocityTheory.Coh.coind_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:10.295353+00:00
-- url     : https://prove2.me/submissions/27ff27b7-c87f-4b38-8222-fd48f5593994

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Theorems.Thm_ReciprocityTheory_Coh_coindEv_isCoind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : CoindStatement.{u} := by
  intro R _ G _ _ _ _ U M
  exact ⟨coindRep U M, coindEv U M, coindEv_isCoind U M⟩
end ReciprocityTheory.Coh
