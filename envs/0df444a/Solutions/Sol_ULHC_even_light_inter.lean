-- Prove2me | solution 1 for ULHC.even_light_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:09.648965+00:00
-- url     : https://prove2.me/submissions/5ab462fe-3bc7-4771-b2c8-ee2b73a321b8

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
import Theorems.Thm_ULHC_inter_iff_even


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hs : Solid V) (hFV : Inside V F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {B : Finset Edge}
    (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0) (hl : ∀ f ∈ B, f ∉ F) {e : Edge}
    (hE : IsEdge V e) (he : e ∈ B) : ¬ Conn F e.p e.q :=
  (inter_iff_even hs hFV x0 hconn hE).2 ⟨B, heven, hl, he⟩
end ULHC
