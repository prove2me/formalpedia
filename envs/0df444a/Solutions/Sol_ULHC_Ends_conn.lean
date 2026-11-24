-- Prove2me | solution 1 for ULHC.Ends.conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:59.206389+00:00
-- url     : https://prove2.me/submissions/d077315c-fe9d-4dfc-8f82-cef1bf1978fa

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_Conn_of_edge


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {F : Finset Edge} (h : Ends e u v) (he : e ∈ F) : Conn F u v :=
  (h.conn_iff F).1 (Conn.of_edge he)
end Ends
end ULHC
