-- Prove2me | solution 1 for ULHC.endOK_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:06:22.29126+00:00
-- url     : https://prove2.me/submissions/009b3790-129e-4f3e-8977-b233534ebdb4

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_endCell_isCell
import Theorems.Thm_ULHC_end_alt


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} {q : StripSpec} (hv : ValidStrip V G q) :
    EndOK V G q := by
  intro hev
  obtain ⟨h1, hp, hc, _⟩ := hv
  obtain ⟨l1, l2, b, f⟩ := end_alt (show 2 ≤ q.n by omega) hev hp
  exact ⟨endCell_isCell h1 hc, l1, l2, b, f⟩
end ULHC
