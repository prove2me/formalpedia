-- Prove2me | solution 1 for ULHC.Adj.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:58.278928+00:00
-- url     : https://prove2.me/submissions/80ddf9d8-5e3a-449c-92a6-1b29b584e9de

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Adj
theorem _root_.solution {F F' : Finset Edge} (hs : F ⊆ F') {a b : Pt} (h : Adj F a b) : Adj F' a b := by
  obtain ⟨e, he, h⟩ := h; exact ⟨e, hs he, h⟩
end Adj
end ULHC
