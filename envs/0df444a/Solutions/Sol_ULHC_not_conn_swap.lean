-- Prove2me | solution 1 for ULHC.not_conn_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:17.947262+00:00
-- url     : https://prove2.me/submissions/4e52a4d6-ffb4-405c-ba7f-d17121758d51

import Definitions.Def_ULHC_Iso
import Definitions.Def_ULHC_Strip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {G : Finset Edge} {u v w : Pt} (huw : Conn G u w) (h : ¬ Conn G v u) :
    ¬ Conn G v w := fun h' => h (h'.trans huw.symm)
end ULHC
