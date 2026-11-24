-- Prove2me | solution 1 for ULHC.GridIso.conn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:45.751624+00:00
-- url     : https://prove2.me/submissions/c6f0268f-c20d-444f-a15a-d91ac0385075

import Definitions.Def_ULHC_AFlip
import Definitions.Def_ULHC_Iso
import Theorems.Thm_ULHC_GridIso_conn_map
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_conn_map
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
open ULHC.GridIso
variable (I : GridIso)
namespace ULHC.GridIso
theorem _root_.solution {F : Finset Edge} {u v : Pt} :
    Conn (F.image I.g) (I.f u) (I.f v) ↔ Conn F u v := by
  constructor
  · intro h
    have := I.inv.conn_map h
    simp only [inv, Finset.image_image, I.hf] at this
    have e : (I.ginv ∘ I.g) = id := funext I.hg
    rwa [e, Finset.image_id] at this
  · exact I.conn_map
end ULHC.GridIso
