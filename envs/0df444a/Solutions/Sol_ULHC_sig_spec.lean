-- Prove2me | solution 1 for ULHC.sig_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:18:33.20871+00:00
-- url     : https://prove2.me/submissions/1bca5b0e-f673-482e-b6f5-c92aa3f3a427

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
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
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P) (hT : NoTypeIII V F)
  (o : Bool)
namespace ULHC
theorem _root_.solution {w : Pt} (h : Out F P o w) :
    ∃ so, sig F P o w = nb w so ∧ Cut P (sideEdge w so) ∧ outArc F w so = o := by
  refine ⟨Classical.choose h, by simp [sig, h], (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩
end ULHC
