-- Prove2me | solution 1 for ULHC.Conn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:02.231623+00:00
-- url     : https://prove2.me/submissions/cbbbeb7c-9239-4245-a08b-f4d87e22fc9b

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Adj_mono

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution {F F' : Finset Edge} (hs : F ⊆ F') {a b : Pt} (h : Conn F a b) :
    Conn F' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.mono hs)
end Conn
end ULHC
