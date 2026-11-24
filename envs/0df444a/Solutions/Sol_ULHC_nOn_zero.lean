-- Prove2me | solution 1 for ULHC.nOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:26.530494+00:00
-- url     : https://prove2.me/submissions/f0704341-3fb5-4814-970e-36cf4aa7562c

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_nOn_eq
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
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution {n : ℕ} {e : Edge} (h : ∀ j < n, e ∉ cellE (cellJ c s j)) : nOn c s n e = 0 := by
  rw [nOn_eq c s n _ ∅]
  · simp
  · intro j hj; simp [h j hj]
  · simp
end ULHC
