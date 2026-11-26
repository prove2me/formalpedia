-- Prove2me | solution 1 for Sendov.l1_wsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:21.689584+00:00
-- url     : https://prove2.me/submissions/bdbe9b80-56bf-4fbc-bc04-dae5b8b8fd67

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
import Theorems.Thm_Sendov_l1_padd
import Theorems.Thm_Sendov_l1_map_mul
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nonneg
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsumZ_cons
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
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsumZ_cons

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) (hL : 0 ≤ L) : ∀ (r : List (List ℤ)) (i : ℕ),
    l1 (wsum L i r) ≤ L * l1row r := by
  intro r
  induction r with
  | nil => intro i; simp
  | cons p r ih =>
    intro i
    have hd : (0 : ℤ) < (i : ℤ) + 4 := by positivity
    have hw0 : 0 ≤ L / ((i : ℤ) + 4) := Int.ediv_nonneg hL hd.le
    have hw1 : L / ((i : ℤ) + 4) ≤ L := Int.ediv_le_self _ hL
    have h1 := l1_padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r)
    rw [l1_map_mul, abs_of_nonneg hw0] at h1
    have h2 := ih (i + 1)
    have hp := l1_nonneg p
    have hr := l1row_nonneg r
    simp only [wsum_cons, l1row_cons]
    nlinarith [h1, h2, hw0, hw1, hp, hr]
end Sendov
