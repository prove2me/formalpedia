-- Prove2me | solution 1 for ULHC.other_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:56.799443+00:00
-- url     : https://prove2.me/submissions/f7e1dabe-b64d-4aa0-85c0-d29d035ef4e4

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Edge_p_ne_q
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {e : Edge} {y : Pt} (hy : e.p = y ∨ e.q = y) : other e y ≠ y := by
  unfold other
  split_ifs with h
  · subst h; exact (Edge.p_ne_q e).symm
  · rcases hy with hy | hy
    · exact absurd hy h
    · subst hy; exact Edge.p_ne_q e
end ULHC
