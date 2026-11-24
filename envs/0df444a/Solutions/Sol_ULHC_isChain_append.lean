-- Prove2me | solution 1 for ULHC.isChain_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:27:14.710767+00:00
-- url     : https://prove2.me/submissions/1fdb8d05-bf3b-4684-a1c9-e1d76cf21327

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
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
theorem _root_.solution {R : Pt → Pt → Prop} {u : Pt} {l : List Pt} {d : Pt}
    (h : List.IsChain R (u :: l)) (hd : R ((u :: l).getLast (by simp)) d) :
    List.IsChain R (u :: (l ++ [d])) := by
  induction l generalizing u with
  | nil => simpa using hd
  | cons v l ih =>
    rw [List.isChain_cons_cons] at h
    rw [List.cons_append, List.isChain_cons_cons]
    exact ⟨h.1, ih h.2 (by simpa using hd)⟩
end ULHC
