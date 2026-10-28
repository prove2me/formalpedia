-- Prove2me | solution 1 for RuralPostman.NPC.theorem_rpp_np_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:30:19.448795+00:00
-- url     : https://prove2.me/submissions/098ad8ac-bfbd-4463-b964-f98b5d94b34e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_RuralPostman_NPC_Instances
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_RuralPostman_NPC_uhc_polyReducible_urp
import Theorems.Thm_RuralPostman_NPC_dhc_polyReducible_drp
import Theorems.Thm_RuralPostman_NPC_urp_mem_NP
import Theorems.Thm_RuralPostman_NPC_drp_mem_NP

open RuralPostman.NPC

theorem solution (hU : CookPvsNP.NPComplete uhcLang)
    (hD : CookPvsNP.NPComplete dhcLang) :
    CookPvsNP.NPComplete urpLang ∧ CookPvsNP.NPComplete drpLang :=
  ⟨CookPvsNP.npComplete_of_polyReducible uhcLang urpLang hU urp_mem_NP uhc_polyReducible_urp,
   CookPvsNP.npComplete_of_polyReducible dhcLang drpLang hD drp_mem_NP dhc_polyReducible_drp⟩
