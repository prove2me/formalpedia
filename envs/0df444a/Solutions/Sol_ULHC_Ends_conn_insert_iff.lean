-- Prove2me | solution 1 for ULHC.Ends.conn_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:20.491504+00:00
-- url     : https://prove2.me/submissions/b7ac4ea4-30a9-4db0-b11f-561341209e62

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_conn_insert


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {F : Finset Edge} (h : Ends e u v) (x y : Pt) :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x u ∧ Conn F v y) ∨ (Conn F x v ∧ Conn F u y) := by
  rw [conn_insert]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  tauto
end Ends
end ULHC
