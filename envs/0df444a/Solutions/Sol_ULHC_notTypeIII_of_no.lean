-- Prove2me | solution 1 for ULHC.notTypeIII_of_no
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:44:47.159436+00:00
-- url     : https://prove2.me/submissions/c9c09072-ee01-408f-9edb-1eb1eb5685df

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
omit hs hH hHam
namespace ULHC
theorem _root_.solution {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ d, IsCell V d ∧ ¬ NotTypeIII V F d := by
  unfold NoTypeIII at h
  push Not at h
  obtain ⟨c, hc, s, hb, hf, hl1, hl2, hn⟩ := h
  exact ⟨c, hc, fun h' => hn (h' s hb hf hl1 hl2)⟩
end ULHC
