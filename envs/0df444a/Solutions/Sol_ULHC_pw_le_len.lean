-- Prove2me | solution 1 for ULHC.pw_le_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:45.450816+00:00
-- url     : https://prove2.me/submissions/c539ba7a-46ec-4f49-a45e-670c2aac08fe

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_MP_pw_cons
import Theorems.Thm_ULHC_MP_pw_nil
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {l : List Node} {M : ℕ} (h : ∀ x ∈ l, gw x ≤ M) :
    MP.pw gw l ≤ l.length * M := by
  induction l with
  | nil => simp [MP.pw_nil]
  | cons x l ih =>
    rw [MP.pw_cons, List.length_cons, Nat.succ_mul]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega
end ULHC
