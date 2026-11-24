-- Prove2me | solution 1 for ULHC.preach_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:41:01.254877+00:00
-- url     : https://prove2.me/submissions/0825012c-9bbd-48a1-be64-a75ff4845ef7

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
theorem _root_.solution {x y : Pt × Bool} (h : Relation.ReflTransGen (PStep V B) x y) :
    Relation.ReflTransGen (PStep V B) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hbc.symm B) ih
end ULHC
