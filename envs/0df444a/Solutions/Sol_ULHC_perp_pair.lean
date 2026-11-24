-- Prove2me | solution 1 for ULHC.perp_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:15.246571+00:00
-- url     : https://prove2.me/submissions/aad919e8-90ba-4cd5-bc31-a8bf7dbcb968

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
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
open Finset
namespace ULHC
theorem _root_.solution (d : Pt) {s tf : Side} (ht : tf = latA s ∨ tf = latB s) :
    (back1 d tf = back1 d s ∧ front1 d tf = back2 d s) ∨
      (back1 d tf = back2 d s ∧ front1 d tf = back1 d s) ∨
      (back1 d tf = front1 d s ∧ front1 d tf = front2 d s) ∨
      (back1 d tf = front2 d s ∧ front1 d tf = front1 d s) := by
  obtain ⟨x, y⟩ := d
  rcases ht with rfl | rfl <;> cases s <;> simp [back1, front1, back2, front2, latA, latB]
end ULHC
