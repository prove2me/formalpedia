-- Prove2me | solution 1 for ULHC.nOn_lat2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:42:14.226804+00:00
-- url     : https://prove2.me/submissions/fc40c156-6961-4330-860d-09598b28c0d4

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
import Theorems.Thm_ULHC_lat2_mem_self
import Theorems.Thm_ULHC_lat2_not_mem
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
theorem _root_.solution {n j : ℕ} (hj : j < n) : nOn c s n (lat2 (cellJ c s j) s) = 1 := by
  rw [nOn_eq c s n _ {j}]
  · simp
  · intro m _
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact lat2_not_mem c s (j := j) (m := m) (Ne.symm hne) h
    · intro h; subst h; exact lat2_mem_self c s _
  · simpa using hj
end ULHC
