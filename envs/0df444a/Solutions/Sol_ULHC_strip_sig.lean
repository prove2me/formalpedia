-- Prove2me | solution 1 for ULHC.strip_sig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:28.987679+00:00
-- url     : https://prove2.me/submissions/83896968-0ced-4dde-939d-d5a359ca4ca1

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellJ_zero
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {z : Pt} {tf : Side} {m i : ℕ} (hp : StripPat F z tf m)
    (hi : i < m) :
    (lat1 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧ (lat2 (cellJ z tf i) tf ∈ F ↔ i % 2 = 1) ∧
      (back (cellJ z tf i) tf ∈ F ↔ i % 2 = 0) ∧
      (front (cellJ z tf i) tf ∈ F ↔ (i % 2 = 1 ↔ i + 1 < m)) := by
  obtain ⟨hb, hl, hf⟩ := hp
  refine ⟨(hl i hi).1, (hl i hi).2, ?_, hf i hi⟩
  rcases i with _ | j
  · rw [cellJ_zero]; simp [hb]
  · rw [back_cellJ_succ, hf j (by omega)]; omega
end ULHC
