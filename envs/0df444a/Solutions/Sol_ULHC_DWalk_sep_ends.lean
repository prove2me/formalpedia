-- Prove2me | solution 1 for ULHC.DWalk.sep_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:58.941793+00:00
-- url     : https://prove2.me/submissions/e22d5304-4c6d-4b4e-890b-22bba486e723

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
import Theorems.Thm_ULHC_DWalk_sep
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_Ends_isEdge
import Theorems.Thm_ULHC_GridIso_conn_iff


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
namespace DWalk
theorem _root_.solution (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} {u v : Pt} (hE : Ends e u v) (he : e ∈ B) (hu : u ∈ V) (hv : v ∈ V) :
    ¬ Conn F u v := by
  rw [← hE.conn_iff]
  exact h.sep hs hFV x0 hconn he (hE.isEdge hu hv)
end DWalk
end ULHC
