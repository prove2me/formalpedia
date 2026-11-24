-- Prove2me | solution 1 for ULHC.Good.isCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:51.489806+00:00
-- url     : https://prove2.me/submissions/7756daf2-34fc-45cc-a930-68e9c20f0ee7

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_Deg2_factor
import Theorems.Thm_ULHC_D_eq_zero_of_not_cell
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} (hF : Deg2 V F) (hH : Deg2 V H)
include hF hH
namespace ULHC
namespace Good
theorem _root_.solution (hs : Solid V) {o : Bool} {c : Pt} (hg : Good o (D F H c)) : IsCell V c := by
  by_contra h
  have := D_eq_zero_of_not_cell hF.factor hH.factor hs h
  unfold Good at hg; rw [this] at hg
  cases o <;> simp at hg
end Good
end ULHC
