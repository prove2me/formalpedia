-- Prove2me | solution 1 for ULHC.Ends.insert_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:34.203124+00:00
-- url     : https://prove2.me/submissions/da22f8de-456d-49e5-bdfa-a6198b2f8fa5

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_conn_insert_of_conn


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {F : Finset Edge} (h : Ends e u v) (hc : Conn F u v) (x y : Pt) :
    Conn (insert e F) x y ↔ Conn F x y :=
  conn_insert_of_conn ((h.conn_iff F).2 hc) x y
end Ends
end ULHC
