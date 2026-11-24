-- Prove2me | solution 1 for ULHC.isCell_of_corners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:07:06.786108+00:00
-- url     : https://prove2.me/submissions/f8c62688-bb50-4d3e-a852-8a5c2788b6fa

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} (c : Pt) (s : Side)
    (h1 : back1 c s ∈ V) (h2 : back2 c s ∈ V) (h3 : front1 c s ∈ V) (h4 : front2 c s ∈ V) :
    IsCell V c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [back1, back2, front1, front2] at h1 h2 h3 h4 <;>
    exact ⟨by assumption, by assumption, by assumption, by assumption⟩
end ULHC
