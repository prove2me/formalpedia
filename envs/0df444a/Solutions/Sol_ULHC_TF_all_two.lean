-- Prove2me | solution 1 for ULHC.TF.all_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:02.090297+00:00
-- url     : https://prove2.me/submissions/6fdbe4cd-3583-418f-af84-7c41c110989f

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
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
theorem _root_.solution {S : Finset Pt} {f : Pt → ℕ} (hle : ∀ z ∈ S, f z ≤ 2)
    (hsum : 2 * S.card ≤ ∑ z ∈ S, f z) : ∀ z ∈ S, f z = 2 := by
  have hle' : ∑ z ∈ S, f z ≤ ∑ z ∈ S, 2 := sum_le_sum hle
  have heq : ∑ z ∈ S, f z = ∑ z ∈ S, (fun _ => 2) z := by
    simp only [sum_const, smul_eq_mul] at hle' ⊢
    omega
  exact (sum_eq_sum_iff_of_le hle).1 heq
end ULHC.TF
