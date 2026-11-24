-- Prove2me | solution 1 for ULHC.Border.same_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:19:21.979032+00:00
-- url     : https://prove2.me/submissions/03208962-6f6e-4ad8-a5b7-6683beae2831

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_Border_mem_of_conn
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Border
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {x y : Pt} (h : Conn F x y) : (x ∈ P ↔ y ∈ P) :=
  ⟨fun hx => hB.mem_of_conn hx h, fun hy => hB.mem_of_conn hy h.symm⟩
end Border
end ULHC
