-- Prove2me | solution 1 for ULHC.flipCol_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:13.75895+00:00
-- url     : https://prove2.me/submissions/753299ca-3d26-4360-bb06-5cfea1c3495e

import Definitions.Def_ULHC_Cr2
import Definitions.Def_ULHC_CrPath
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_mem_flipCol
import Theorems.Thm_ULHC_nOn_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (G : Finset Edge) (c : Pt) (s : Side) (n : ℕ) {e : Edge}
    (h : ∀ i, i + 1 < n + 1 → e ∉ cellE (cellJ c s i)) :
    e ∈ flipCol G c s (n + 1) ↔ e ∈ flip G (cellJ c s n) := by
  rw [mem_flipCol, mem_flip_iff]
  by_cases he : e ∈ cellE (cellJ c s n)
  · rw [nOn_eq c s (n + 1) e {n} (fun j hj => by
      constructor
      · intro h'
        by_contra hne
        exact h j (by simp at hne; omega) h'
      · intro h'; simp at h'; subst h'; exact he) (by simp)]
    simp [he]
  · rw [nOn_eq c s (n + 1) e ∅ (fun j hj => by
      constructor
      · intro h'
        rcases (show j < n ∨ j = n by omega) with hj' | rfl
        · exact absurd h' (h j (by omega))
        · exact absurd h' he
      · intro h'; simp at h') (by simp)]
    simp [he]
end ULHC
