-- Prove2me | solution 1 for ULHC.inter_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:12.292675+00:00
-- url     : https://prove2.me/submissions/e52c3bc5-ea6d-41d5-8cd1-3cdfa4cad90c

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_cut_sides_even
import Theorems.Thm_ULHC_Border_not_cut
import Theorems.Thm_ULHC_Border_same_side
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_separation
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {e : Edge} (hE : IsEdge V e) :
    ¬ Conn F e.p e.q ↔ ∃ B : Finset Edge, (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧
      (∀ f ∈ B, f ∉ F) ∧ e ∈ B := by
  constructor
  · intro hn
    set P := cls V F e.p
    have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hFV _ u hu w hw⟩
    refine ⟨(GE V).filter (Cut P), cut_sides_even P _ (fun f => by
      rw [Finset.mem_filter, mem_GE]) , fun f hf hfF => ?_, ?_⟩
    · rw [Finset.mem_filter] at hf
      exact hB.not_cut hfF hf.2
    · rw [Finset.mem_filter, mem_GE]
      refine ⟨hE, ?_⟩
      have hp : e.p ∈ P := mem_cls_self hE.1
      have hq : e.q ∉ P := by
        simp only [P, cls, Finset.mem_filter, not_and]; exact fun _ => hn
      unfold Cut; tauto
  · rintro ⟨B, heven, hlight, he⟩ hc
    obtain ⟨P, hB, hcut⟩ := separation B hs heven hFV hlight x0 hconn
    have := (hcut e hE).2 he
    unfold Cut at this
    have := hB.same_side hc
    tauto
end ULHC
