-- Prove2me | solution 1 for ULHC.conn_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:06.670099+00:00
-- url     : https://prove2.me/submissions/7c16d62b-beac-465b-b657-759583af9026

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F F' : Finset Edge} (f : Pt → Pt)
    (h : ∀ u v, Adj F u v → Conn F' (f u) (f v)) {x y : Pt} (hxy : Conn F x y) :
    Conn F' (f x) (f y) := by
  induction hxy with
  | refl => exact Conn.refl _ _
  | tail _ hyz ih => exact ih.trans (h _ _ hyz)
end ULHC
