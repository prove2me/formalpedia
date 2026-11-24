-- Prove2me | solution 1 for ULHC.lift_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:29:19.909501+00:00
-- url     : https://prove2.me/submissions/06a2de49-bc27-413f-86ae-c6299aa72ebf

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
theorem _root_.solution {a z : Pt} (h : Conn (GE V) a z) (b : Bool) :
    ∃ b', Relation.ReflTransGen (PStep V B) (a, b) (z, b') := by
  induction h with
  | refl => exact ⟨b, Relation.ReflTransGen.refl⟩
  | @tail y w _ hyw ih =>
    obtain ⟨b1, h1⟩ := ih
    exact ⟨b1 ^^ decide (∃ e ∈ B, Ends e y w), h1.tail ⟨hyw, rfl⟩⟩
end ULHC
