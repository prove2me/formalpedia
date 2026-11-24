-- Prove2me | solution 1 for ULHC.sum_hi_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:26:53.345398+00:00
-- url     : https://prove2.me/submissions/ee2cbad9-6f9a-4d33-abda-aab642142f01

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_hi_eq_iff
import Theorems.Thm_ULHC_lo_eq_iff
import Theorems.Thm_ULHC_bot_ne_lft
import Theorems.Thm_ULHC_top_ne_rgt
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
namespace ULHC
theorem _root_.solution (B : Finset Edge) (W : Pt → ℤ) (T : Finset Pt)
    (hT : ∀ e ∈ B, e.hi ∈ T ∧ e.lo ∈ T) :
    ∑ e ∈ B, (W e.hi + W e.lo) = ∑ c ∈ T, W c * (sidesIn B c : ℤ) := by
  have h1 : ∀ e ∈ B, W e.hi + W e.lo =
      ∑ c ∈ T, W c * ((if e.hi = c then 1 else 0) + (if e.lo = c then 1 else 0)) := by
    intro e he
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (hT e he).1, if_pos (hT e he).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  simp only [hi_eq_iff, lo_eq_iff]
  unfold sidesIn ind
  have e1 : ∑ e ∈ B, (if e = bot c ∨ e = lft c then (1 : ℤ) else 0) =
      (if bot c ∈ B then 1 else 0) + (if lft c ∈ B then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : B.filter (fun e => e = bot c ∨ e = lft c) =
        (B.filter (· = bot c)) ∪ (B.filter (· = lft c)) := by
      ext e; simp [Finset.mem_filter]; tauto
    rw [this, Finset.card_union_of_disjoint]
    · rw [Finset.filter_eq', Finset.filter_eq']
      split_ifs <;> simp
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact bot_ne_lft c (h1 ▸ h2)
  have e2 : ∑ e ∈ B, (if e = top c ∨ e = rgt c then (1 : ℤ) else 0) =
      (if top c ∈ B then 1 else 0) + (if rgt c ∈ B then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : B.filter (fun e => e = top c ∨ e = rgt c) =
        (B.filter (· = top c)) ∪ (B.filter (· = rgt c)) := by
      ext e; simp [Finset.mem_filter]; tauto
    rw [this, Finset.card_union_of_disjoint]
    · rw [Finset.filter_eq', Finset.filter_eq']
      split_ifs <;> simp
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact top_ne_rgt c (h1 ▸ h2)
  rw [e1, e2]
  push_cast
  split_ifs <;> simp
end ULHC
