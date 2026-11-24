-- Prove2me | solution 1 for ULHC.Adj.ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:08.754531+00:00
-- url     : https://prove2.me/submissions/b012b8b4-9004-48a6-ba52-fa4ce3515a57

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Adj
theorem _root_.solution {G : Finset Edge} {u v : Pt} (h : Adj G u v) : ∃ e ∈ G, Ends e u v := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h⟩
end Adj
end ULHC
