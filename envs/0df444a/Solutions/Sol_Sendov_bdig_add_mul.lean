-- Prove2me | solution 1 for Sendov.bdig_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:33.677342+00:00
-- url     : https://prove2.me/submissions/13c20e4f-0b65-41e8-9f39-0bb6cf92435c

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_unpackZ_succ
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.unpackZ_succ

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b c N : ℤ) (hb : 0 < b) (hc : 2 * |c| < b) :
    bdig b (c + b * N) = c := by
  have hmod : (c + b * N) % b = c % b := Int.add_mul_emod_self_left c b N
  by_cases h : 0 ≤ c
  · rw [abs_of_nonneg h] at hc
    have hcb : c < b := by linarith
    have hx : (c + b * N) % b = c := by rw [hmod, Int.emod_eq_of_lt h hcb]
    simp only [bdig, hx]
    split_ifs
    omega
  · have h' : c < 0 := not_le.1 h
    rw [abs_of_neg h'] at hc
    have hcb : c % b = c + b := by
      have e1 : (c + b) % b = c % b := by simp
      have e2 : (c + b) % b = c + b := Int.emod_eq_of_lt (by linarith) (by linarith)
      omega
    have hx : (c + b * N) % b = c + b := by rw [hmod, hcb]
    simp only [bdig, hx]
    split_ifs <;> omega
end Sendov
