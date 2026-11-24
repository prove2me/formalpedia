-- Prove2me | solution 1 for ULHC.alt_no_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:21:35.425244+00:00
-- url     : https://prove2.me/submissions/4aee9e7a-093e-4b3e-b906-c5068328debd

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_corners_of_side

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT
omit hF
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by
  obtain ⟨h1, h2, h3⟩ := alt_corners_conn hT hw ha
  exact corners_of_side w s P ⟨hB.same_side h1, hB.same_side h2, hB.same_side h3⟩
end ULHC
