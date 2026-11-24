-- Prove2me | solution 1 for ULHC.nOn_front_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:42:17.614426+00:00
-- url     : https://prove2.me/submissions/397430c4-5afa-41bc-b672-04ab260709c5

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_nOn_eq
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_front_mem_self
import Theorems.Thm_ULHC_front_not_mem
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (m : ℕ) : nOn c s (m + 1) (front (cellJ c s m) s) = 1 := by
  rw [nOn_eq c s (m + 1) _ {m}]
  · simp
  · intro j hj
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne
      exact front_not_mem c s (j := m) (m := j) (Ne.symm hne) (by omega) h
    · rintro rfl; exact front_mem_self c s j
  · simp
end ULHC
