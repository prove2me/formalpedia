-- Prove2me | solution 1 for ULHC.Ends.ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:41.521475+00:00
-- url     : https://prove2.me/submissions/5ccb786d-10cb-4f20-b38d-d2349a53b172

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_p_ne_q


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution (h : Ends e u v) : u ≠ v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact Edge.p_ne_q e
  · rw [← h1, ← h2]; exact (Edge.p_ne_q e).symm
end Ends
end ULHC
