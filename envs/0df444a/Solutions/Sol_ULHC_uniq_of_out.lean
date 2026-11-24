-- Prove2me | solution 1 for ULHC.uniq_of_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:11:49.194604+00:00
-- url     : https://prove2.me/submissions/a6ec4475-5bcc-4911-84dd-2ddac679bd62

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_no_cut
import Theorems.Thm_ULHC_cut_has_dark_lat
import Theorems.Thm_ULHC_step_cell
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
include hF hB hT
namespace ULHC
theorem _root_.solution {w : Pt} (hw : IsCell V w) (si : Side) (hcut : Cut P (sideEdge w si))
    (hin : outArc F w si = !o) (hout : Out F P o w) :
    ∀ s1 s2, Cut P (sideEdge w s1) → outArc F w s1 = !o →
      Cut P (sideEdge w s2) → outArc F w s2 = !o → s1 = s2 := by
  rcases step_cell hB w o (fun s h => cut_has_dark_lat hF hB hT hw s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, _, _, h4⟩ | ⟨_, _, _, _, _, _, _, _, hall'⟩
  · exact fun s1 s2 c1 o1 c2 o2 => (h4 s1 c1 o1).trans (h4 s2 c2 o2).symm
  · obtain ⟨so', hc', ho'⟩ := hout
    have := hall' so' hc'
    rw [ho'] at this
    cases o <;> simp at this
end ULHC
