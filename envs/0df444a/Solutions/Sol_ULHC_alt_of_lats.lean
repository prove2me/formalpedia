-- Prove2me | solution 1 for ULHC.alt_of_lats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:04.904643+00:00
-- url     : https://prove2.me/submissions/659c06fe-6ae1-460d-a3eb-0cf028f7ae16

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {u : Pt} {tf : Side} (l1 : lat1 u tf ∈ F) (l2 : lat2 u tf ∈ F)
    (b : back u tf ∉ F) (f : front u tf ∉ F) : Alt F u := by
  rw [lat1_eq] at l1; rw [lat2_eq] at l2
  simp only [back, front] at b f
  cases tf <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 b f <;> unfold Alt <;> tauto
end ULHC
