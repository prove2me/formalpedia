-- Prove2me | solution 1 for ULHC.T.lsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:44.490546+00:00
-- url     : https://prove2.me/submissions/12d1a531-ccfc-43a8-8053-8d8165bc8962

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_tick
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
theorem _root_.solution {γ : Type} (l : List γ) (g : γ → ℕ) (c : ℕ) (h : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    omega
end ULHC.T
