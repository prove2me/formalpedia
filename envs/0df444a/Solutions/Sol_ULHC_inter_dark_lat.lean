-- Prove2me | solution 1 for ULHC.inter_dark_lat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:11:46.462708+00:00
-- url     : https://prove2.me/submissions/ac097b08-dd1d-4828-b9f3-cb350980e59e

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_closed_cls
import Theorems.Thm_ULHC_cut_has_dark_lat
import Theorems.Thm_ULHC_mem_cls_self
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F)
include hF hT
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  set e := sideEdge w s
  have hB : Border V F (cls V F e.p) :=
    ⟨Finset.filter_subset _ _, fun u hu v hv => closed_cls hF.1 e.p u hu v hv⟩
  apply cut_has_dark_lat hF hB hT hw s
  unfold Cut
  have hp : e.p ∈ cls V F e.p := mem_cls_self h.1.1
  have hq : e.q ∉ cls V F e.p := by
    simp only [cls, Finset.mem_filter, not_and]; exact fun _ => h.2.2
  tauto
end ULHC
