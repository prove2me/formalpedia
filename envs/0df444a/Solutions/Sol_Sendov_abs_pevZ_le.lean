-- Prove2me | solution 1 for Sendov.abs_pevZ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:09.384387+00:00
-- url     : https://prove2.me/submissions/4a0b205f-21f1-411e-9740-09dfb7085c39

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
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
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
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.qrow_length

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b : ℤ) (hb : 1 ≤ b) :
    ∀ p : List ℤ, |pevZ p b| ≤ l1 p * b ^ p.length := by
  intro p
  induction p with
  | nil => simp
  | cons a p ih =>
    have hb0 : (0 : ℤ) < b := by omega
    have hpow : (1 : ℤ) ≤ b ^ p.length := one_le_pow₀ hb
    have hl1 := l1_nonneg p
    have habs := abs_nonneg a
    calc |pevZ (a :: p) b| = |a + b * pevZ p b| := rfl
      _ ≤ |a| + |b * pevZ p b| := abs_add_le _ _
      _ = |a| + b * |pevZ p b| := by rw [abs_mul, abs_of_pos hb0]
      _ ≤ |a| + b * (l1 p * b ^ p.length) := by nlinarith [ih]
      _ ≤ (|a| + l1 p) * b ^ (p.length + 1) := by
            have hbb : (1 : ℤ) ≤ b * b ^ p.length := by nlinarith [hpow, hb0]
            have hkey := mul_le_mul_of_nonneg_left hbb habs
            ring_nf
            nlinarith [hkey, hpow, hl1, hb0]
      _ = l1 (a :: p) * b ^ (a :: p).length := by simp [l1_cons]
end Sendov
