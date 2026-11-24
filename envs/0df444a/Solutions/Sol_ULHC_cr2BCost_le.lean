-- Prove2me | solution 1 for ULHC.cr2BCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:57.045793+00:00
-- url     : https://prove2.me/submissions/b68073ff-3f3a-4299-b033-f202609ab35a

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_allStripsCost_le
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_connBCost_le
import Theorems.Thm_ULHC_endCell_isCell


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) {b c : StripSpec} (hb1 : 1 ≤ b.n) (hbn : b.n ≤ V.card)
    (hb : ∀ j < b.n, IsCell V (cellJ b.c b.s j)) (hcn : c.n ≤ V.card) :
    cr2BCost V G b c ≤ 270 * (V.card + 1) ^ 2 := by
  have hu := endCell_isCell hb1 hb
  have h1 := allStripsCost_le V (flip G (endCell b))
  have h2 := connBCost_le hGV (back1 c.c c.s)
  have h3 := connBCost_le (inside_flip hGV hu) (back1 c.c c.s)
  unfold cr2BCost sideOffBCost notEndBCost endOffBCost midBCost flipCost
  nlinarith
end ULHC
