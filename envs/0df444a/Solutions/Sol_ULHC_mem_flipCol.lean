-- Prove2me | solution 1 for ULHC.mem_flipCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:21.62353+00:00
-- url     : https://prove2.me/submissions/bd3c0a4b-b4d8-4a6f-b460-17961238e09c

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_flipCol_succ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ n e, e ∈ flipCol F c s n ↔ (e ∈ F ↔ nOn c s n e % 2 = 0) := by
  intro n
  induction n generalizing F with
  | zero => intro e; simp [flipCol, nOn]
  | succ n ih =>
    intro e
    rw [flipCol_succ, ih, mem_flip_iff]
    unfold nOn
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      set X := ((Finset.range n).filter (fun j => e ∈ cellE (cellJ c s j))).card
      have hx : ((X + 1) % 2 = 0) ↔ ¬ (X % 2 = 0) := by omega
      rw [hx]; tauto
    · tauto
end ULHC
