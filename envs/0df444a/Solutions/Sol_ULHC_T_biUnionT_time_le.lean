-- Prove2me | solution 1 for ULHC.T.biUnionT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:04.56862+00:00
-- url     : https://prove2.me/submissions/75f887e6-bf02-46e5-ac00-be26f4f726aa

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_tick
import Theorems.Thm_ULHC_T_fsum_le
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


attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.time_tick

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution [DecidableEq β] (f : α → TimeM (Finset β)) (s : Finset α) (c d : ℕ)
    (h : ∀ x ∈ s, (f x).time ≤ c) (hd : ∀ x ∈ s, (f x).ret.card ≤ d) :
    (biUnionT f s).time ≤ s.card * (c + d + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; have := hd x hx; dsimp only; omega)
end ULHC.T
