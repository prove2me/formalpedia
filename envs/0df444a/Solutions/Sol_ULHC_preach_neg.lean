-- Prove2me | solution 1 for ULHC.preach_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:31:21.601386+00:00
-- url     : https://prove2.me/submissions/4ff54b1b-fc7b-4cdb-bc23-e9c925dcaae9

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_PStep_neg
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
theorem _root_.solution {x y : Pt × Bool} (h : Relation.ReflTransGen (PStep V B) x y) :
    Relation.ReflTransGen (PStep V B) (x.1, !x.2) (y.1, !y.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.neg B)
end ULHC
