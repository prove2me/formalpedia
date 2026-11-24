-- Prove2me | solution 1 for ULHC.Edge.eq_of_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:26:02.193039+00:00
-- url     : https://prove2.me/submissions/64e9a859-595a-4c5f-a7e9-92298abe8a3e

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_q_sum
import Theorems.Thm_ULHC_Edge_ext_pq
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Edge
theorem _root_.solution {e e' : Edge} {u v : Pt} (h : Ends e u v) (h' : Ends e' u v) : e = e' := by
  have s1 := Edge.q_sum e
  have s2 := Edge.q_sum e'
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h' with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Edge.ext_pq (a1.trans b1.symm) (a2.trans b2.symm)
  · rw [a1, a2] at s1; rw [b1, b2] at s2; omega
  · rw [a1, a2] at s1; rw [b1, b2] at s2; omega
  · exact Edge.ext_pq (a1.trans b1.symm) (a2.trans b2.symm)
end Edge
end ULHC
