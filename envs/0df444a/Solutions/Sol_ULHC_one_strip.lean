-- Prove2me | solution 1 for ULHC.one_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:18:35.467683+00:00
-- url     : https://prove2.me/submissions/8d378673-61bf-46f7-8db1-7dcf3ded6f06

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_conn_of_ncomp_one
import Theorems.Thm_ULHC_exists_not_conn
import Theorems.Thm_ULHC_exists_cut_edge
import Theorems.Thm_ULHC_edge_cells
import Theorems.Thm_ULHC_Border_not_cut
import Theorems.Thm_ULHC_D_even
import Theorems.Thm_ULHC_D_jump
import Theorems.Thm_ULHC_Deg2_factor
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_mem_cls_self
import Theorems.Thm_ULHC_phase1
import Theorems.Thm_ULHC_phase2
import Theorems.Thm_ULHC_strip_mu
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
namespace ULHC
theorem _root_.solution {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F) (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_conn h2
  set P := cls V F x
  have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hF.1 x u hu w hw⟩
  have hxP : x ∈ P := mem_cls_self hx
  have hyP : y ∉ P := by simp only [P, cls, Finset.mem_filter, not_and]; exact fun _ => hxy
  obtain ⟨e, heH, hcut⟩ := exists_cut_edge (conn_of_ncomp_one hHam hx hy) hxP hyP
  have heF : e ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨sh, sl, h1, h2', h3, h4, h5, h6⟩ := edge_cells F e
  have hjump := D_jump hF.factor hH.factor e
  have hw : wD F H e = if up F e then 2 else -2 := by
    unfold wD wb; simp [heF, heH]
  rw [hw] at hjump
  -- Choose the orientation from the sign of `D` at the arc's tail.
  have key : ∃ o v s0, Cut P (sideEdge v s0) ∧ outArc F v s0 = !o ∧
      (if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2) ∧
      Good o (D F H v) := by
    -- `a` is the tail of the arc across `e`, `b` its head; `D b = D a + 2`.
    obtain ⟨a, b, sa, sb, ha1, ha2, ha3, hb1, hb2, hb3, hD⟩ :
        ∃ a b sa sb, sideEdge a sa = e ∧ nb a sa = b ∧ outArc F a sa = true ∧
          sideEdge b sb = e ∧ nb b sb = a ∧ outArc F b sb = false ∧
          D F H b = D F H a + 2 := by
      cases hu : up F e
      · refine ⟨e.hi, e.lo, sh, sl, h1, h2', by rw [h3, hu]; rfl, h4, h5, by rw [h6, hu], ?_⟩
        rw [hu] at hjump; simp at hjump; omega
      · refine ⟨e.lo, e.hi, sl, sh, h4, h5, by rw [h6, hu], h1, h2', by rw [h3, hu]; rfl, ?_⟩
        rw [hu] at hjump; simp at hjump; omega
    by_cases hpos : 0 ≤ D F H a
    · refine ⟨true, b, sb, by rw [hb1]; exact hcut, by rw [hb3]; rfl, ?_, ?_⟩
      · simp only [ite_true]; rw [hb2]; exact hD
      · unfold Good; simp; omega
    · obtain ⟨m, hm⟩ := D_even F H a
      refine ⟨false, a, sa, by rw [ha1]; exact hcut, by rw [ha3]; rfl, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ite_false]; rw [ha2]; omega
      · unfold Good; simp; omega
  obtain ⟨o, v, s0, hc0, hi0, hj0, hg0⟩ := key
  obtain ⟨w, _, hgw, hst⟩ := phase1 hF hH hs hB hT o v s0 hc0 hi0 hj0 hg0
  obtain ⟨s, n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2 hF hH hs hB hgw hst
  refine ⟨⟨w, s, n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn, ?_⟩
  exact strip_mu hp n hpat hcell hgood
end ULHC
