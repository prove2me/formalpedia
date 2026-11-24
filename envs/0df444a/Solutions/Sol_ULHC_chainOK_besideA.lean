-- Prove2me | solution 1 for ULHC.chainOK_besideA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:15:14.034908+00:00
-- url     : https://prove2.me/submissions/785bf2df-cdad-442d-a839-14ff3ea414df

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_endCell_mk
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_shared_unique
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) :
    ChainOK ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by
  intro j hj z hz hze
  simp only at hj
  obtain rfl : j = 0 := by omega
  rw [cellJ_zero] at hz
  rw [endCell_mk] at hze ⊢
  refine ⟨rfl, Or.inl ?_⟩
  rw [shared_unique rfl hze hz, lat1_eq]
end ULHC
