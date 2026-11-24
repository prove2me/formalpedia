-- Prove2me | solution 1 for ULHC.t3_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:13.77981+00:00
-- url     : https://prove2.me/submissions/67733854-7754-4e3d-a875-4688bd9acea5

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cross_to_back
import Theorems.Thm_ULHC_findT3_some
import Theorems.Thm_ULHC_flip_alt_count
import Theorems.Thm_ULHC_frame_latA
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) {d : Pt} {tf : Side}
    (ht : findT3 V G = some (d, tf)) : ncomp V (flip G d) + 1 = ncomp V G := by
  obtain ⟨hd, hb, hf, hl1, hl2, hnc⟩ := findT3_some hG.1 ht
  obtain ⟨ff, fb, fl⟩ := frame_latA d tf
  have l1 : lat1 d (latA tf) ∈ G := by
    rcases fl with ⟨e1, _⟩ | ⟨e1, _⟩
    · rw [e1]; exact hb
    · rw [e1]; exact hf
  have l2 : lat2 d (latA tf) ∈ G := by
    rcases fl with ⟨_, e2⟩ | ⟨_, e2⟩
    · rw [e2]; exact hf
    · rw [e2]; exact hb
  have bs : back d (latA tf) ∉ G := by rw [fb]; exact hl2
  have fs : front d (latA tf) ∉ G := by rw [ff]; exact hl1
  have ht' : tf = latA (latA tf) ∨ tf = latB (latA tf) := by
    cases tf <;> simp [latA, latB]
  exact (flip_alt_count hG hd l1 l2 bs fs).2 (cross_to_back ht' l1 l2 hnc)
end ULHC
