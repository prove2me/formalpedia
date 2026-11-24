-- Prove2me | solution 1 for ULHC.conn_insert_of_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:04.609428+00:00
-- url     : https://prove2.me/submissions/ec1296b6-1c69-400b-8e09-f81170098101

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_conn_insert
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} (h : Conn F e.p e.q) (x y : Pt) :
    Conn (insert e F) x y ↔ Conn F x y := by
  rw [conn_insert]
  constructor
  · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h'
    · exact (h1.trans h).trans h2
    · exact (h1.trans h.symm).trans h2
  · exact fun h' => Or.inl h'
end ULHC
