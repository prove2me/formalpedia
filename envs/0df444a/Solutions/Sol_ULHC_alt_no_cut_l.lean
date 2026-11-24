-- Prove2me | solution 1 for ULHC.alt_no_cut_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:12.698699+00:00
-- url     : https://prove2.me/submissions/32087899-6f0b-4c38-bc15-4a626170b4ea

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
import Theorems.Thm_ULHC_corners_of_side

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P)
include hF hB
omit hF
namespace ULHC
theorem _root_.solution {w : Pt} (hTw : NotTypeIII V F w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by
  obtain ⟨h1, h2, h3⟩ := alt_corners_conn' hTw ha
  exact corners_of_side w s P ⟨hB.same_side h1, hB.same_side h2, hB.same_side h3⟩
end ULHC
