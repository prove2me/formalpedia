-- Prove2me | solution 1 for Sendov.l1row_qrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:12.420425+00:00
-- url     : https://prove2.me/submissions/93f2fa40-5312-4174-973a-4b5c4dd4aab9

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_wsum_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nonneg
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_qstep
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
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


attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.wsum_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.l1row_cons

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g₀ g₁ g₂ : List ℤ) (k : ℕ) :
    l1row (qrow g₀ g₁ g₂ k) ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k := by
  induction k with
  | zero => simp [qrow]
  | succ k ih =>
    have hg : 0 ≤ l1 g₀ + l1 g₁ + l1 g₂ := by
      have := l1_nonneg g₀; have := l1_nonneg g₁; have := l1_nonneg g₂; omega
    calc l1row (qrow g₀ g₁ g₂ (k + 1))
        ≤ (l1 g₀ + l1 g₁ + l1 g₂) * l1row (qrow g₀ g₁ g₂ k) := l1row_qstep _ _ _ _
      _ ≤ (l1 g₀ + l1 g₁ + l1 g₂) * (l1 g₀ + l1 g₁ + l1 g₂) ^ k := by
          exact mul_le_mul_of_nonneg_left ih hg
      _ = (l1 g₀ + l1 g₁ + l1 g₂) ^ (k + 1) := by ring
end Sendov
