-- Prove2me | solution 1 for ULHC.exists_not_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:19:52.258809+00:00
-- url     : https://prove2.me/submissions/aab55c75-7c08-401b-9a3c-fcb561ab2592

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_cellJ_inj
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
namespace ULHC
theorem _root_.solution (V : Finset Pt) (c : Pt) (s : Side) : ∃ J, ¬ IsCell V (cellJ c s J) := by
  by_contra h
  push Not at h
  have hmaps : ∀ k ∈ Finset.range (V.card + 1), cellJ c s k ∈ V := fun k _ => (h k).1
  have hinj : Set.InjOn (cellJ c s) (Finset.range (V.card + 1)) :=
    fun i _ j _ hij => cellJ_inj c s hij
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simp at this
end ULHC
