-- Prove2me | solution 1 for Sendov.integral_moment_packed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:00.643494+00:00
-- url     : https://prove2.me/submissions/a0ee707d-7f6c-441a-b291-e71c168599ff

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_pev_wsum
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_integral_moment_of
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_three_add_pos
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero


attribute [local simp] Sendov.qrow_length

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (L : ℤ) (hL : 0 < L) (Nmom : List ℤ)
    (hdvd : ∀ j, j < 2 * k + 1 → ((0 : ℕ) + j + 4 : ℤ) ∣ L)
    (hNmom : pev Nmom α = pev (wsum L 0 (qrow (gg0 n) (gg1 n) (gg2 n) k)) α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = pev Nmom α / ((L : ℝ) * (2 * M n * (3 + α)) ^ k) := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hD : (0 : ℝ) < 2 * M n * (3 + α) := by positivity
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hdvd' : ∀ j, j < (qrow (gg0 n) (gg1 n) (gg2 n) k).length →
      ((0 : ℕ) + j + 4 : ℤ) ∣ L := by
    intro j hj
    rw [qrow_length] at hj
    exact hdvd j hj
  have hw := pev_wsum L (qrow (gg0 n) (gg1 n) (gg2 n) k) 0 α hdvd'
  rw [integral_moment_of n k hn α hα, hNmom, hw]
  field_simp
end Sendov
