-- Prove2me | solution 1 for ULHC.par_cellJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:20:50.630885+00:00
-- url     : https://prove2.me/submissions/2416beef-46de-4a42-8ae1-66438746adca

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_par_nb
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_nb_cellJ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) (j : ℕ) :
    par (cellJ c s j) = (par c ^^ decide (j % 2 = 1)) := by
  induction j with
  | zero => simp [cellJ_zero]
  | succ j ih =>
    rw [← nb_cellJ, par_nb, ih]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have : (j + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (j + 1) % 2 = 0 := by omega
      simp [h, this]
end ULHC
