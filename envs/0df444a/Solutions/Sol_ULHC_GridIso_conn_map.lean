-- Prove2me | solution 1 for ULHC.GridIso.conn_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:07.023784+00:00
-- url     : https://prove2.me/submissions/cf2773a1-306c-4f5c-a4b8-4ae064d86743

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Theorems.Thm_ULHC_GridIso_adj_map
import Theorems.Thm_ULHC_Conn_of_adj
import Theorems.Thm_ULHC_conn_map


set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)
namespace ULHC.GridIso
theorem _root_.solution {F : Finset Edge} {u v : Pt} (h : Conn F u v) :
    Conn (F.image I.g) (I.f u) (I.f v) :=
  ULHC.conn_map I.f (fun _ _ h => Conn.of_adj (I.adj_map h)) h
end ULHC.GridIso
