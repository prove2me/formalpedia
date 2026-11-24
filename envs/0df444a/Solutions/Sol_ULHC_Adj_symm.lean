-- Prove2me | solution 1 for ULHC.Adj.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:35.779311+00:00
-- url     : https://prove2.me/submissions/a54c9c6a-69da-4887-b64f-c61559c3d449

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Adj
theorem _root_.solution {F : Finset Edge} {a b : Pt} (h : Adj F a b) : Adj F b a := by
  obtain ⟨e, he, h⟩ := h; exact ⟨e, he, h.symm⟩
end Adj
end ULHC
