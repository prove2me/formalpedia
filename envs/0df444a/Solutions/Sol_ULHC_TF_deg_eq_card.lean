-- Prove2me | solution 1 for ULHC.TF.deg_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:40.673617+00:00
-- url     : https://prove2.me/submissions/39e552e5-4b05-4384-b48a-82ceedd08649

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_deg_empty
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
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution (F : Finset Edge) (z : Pt) :
    deg F z = (F.filter (fun e => e.p = z ∨ e.q = z)).card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [deg_empty]
  | insert e F he ih =>
    rw [deg_insert he, ih, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' => he (mem_filter.1 h').1)]
    · rfl
end ULHC.TF
