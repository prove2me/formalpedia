-- Prove2me | solution 1 for ULHC.DWalk.sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:44.329477+00:00
-- url     : https://prove2.me/submissions/d10dceca-5147-42db-9d6b-806230c54b86

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_DStep_parity
import Theorems.Thm_ULHC_DStep_light
import Theorems.Thm_ULHC_DWalk_parity
import Theorems.Thm_ULHC_DWalk_light
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_separation


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DWalk
theorem _root_.solution (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} (he : e ∈ B) (hE : IsEdge V e) : ¬ Conn F e.p e.q := by
  have heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0 := by
    intro c hc
    rw [h.parity c hc]
    split_ifs <;> rfl
  obtain ⟨P, hB, hcut⟩ := separation B hs heven hFV h.light x0 hconn
  intro hc
  have := (hcut e hE).2 he
  unfold Cut at this
  have := hB.same_side hc
  tauto
end DWalk
end ULHC
