-- Prove2me | solution 1 for ULHC.suf_pat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:23.689514+00:00
-- url     : https://prove2.me/submissions/455d8ded-685f-42c5-9fb9-12e0d0ad4bda

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
import Theorems.Thm_ULHC_cellJ_add
import Theorems.Thm_ULHC_suf_cellJ
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_strip_sig
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {z : StripSpec} {i i0 : ℕ}
namespace ULHC
theorem _root_.solution (hp : StripPat F z.c z.s z.n) (he : i % 2 = 0) (hi : i < z.n) :
    StripPat F (suf z i).c (suf z i).s (suf z i).n := by
  obtain ⟨_, _, gb, _⟩ := strip_sig hp hi
  obtain ⟨_, hl, hf⟩ := hp
  refine ⟨gb.2 he, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [suf] at hj
    rw [suf_cellJ]
    have := hl (i + j) (by omega)
    simp only [suf]; constructor
    · rw [this.1]; omega
    · rw [this.2]; omega
  · simp only [suf] at hj ⊢
    rw [cellJ_add, hf (i + j) (by omega)]
    omega
end ULHC
