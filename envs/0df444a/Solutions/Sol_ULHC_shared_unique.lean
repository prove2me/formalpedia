-- Prove2me | solution 1 for ULHC.shared_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:48.1376+00:00
-- url     : https://prove2.me/submissions/81ab97a9-c7a5-43ad-83a8-ef3e1f64d94a

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {d u : Pt} {tf : Side} (hu : u = nb d tf) {x : Edge} (hx : x ∈ cellE d)
    (hx' : x ∈ cellE u) : x = sideEdge d tf := by
  subst hu
  obtain ⟨p, q⟩ := d
  rw [cellE_frame (p, q) tf] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exfalso; revert hx'
    cases tf <;> simp [cellE, back, sideEdge, nb, Side.opp, bot, top, lft, rgt] <;> omega
  · rfl
  · exfalso; revert hx'
    cases tf <;> simp [cellE, lat1, nb, bot, top, lft, rgt] <;> omega
  · exfalso; revert hx'
    cases tf <;> simp [cellE, lat2, nb, bot, top, lft, rgt] <;> omega
end ULHC
