-- Prove2me | solution 1 for ULHC.Ends.conn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:29.988579+00:00
-- url     : https://prove2.me/submissions/289bccf5-4935-4269-bfc5-eb1ead0b913e

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution (h : Ends e u v) (F : Finset Edge) : Conn F e.p e.q ↔ Conn F u v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact ⟨Conn.symm, Conn.symm⟩
end Ends
end ULHC
