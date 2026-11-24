-- Prove2me | solution 1 for ULHC.Conn.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:55.30326+00:00
-- url     : https://prove2.me/submissions/c4cc5c60-2e55-4b68-ae5e-bdc00290f501

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_refl

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Conn
theorem _root_.solution {F : Finset Edge} {a b : Pt} (h : Conn F a b) : Conn F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih
end Conn
end ULHC
