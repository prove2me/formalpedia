-- Prove2me | solution 1 for Sendov.pev_wsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:10:04.764419+00:00
-- url     : https://prove2.me/submissions/ab5591ae-76c6-4e65-befa-5c0d3abf246a

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_wsum_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_map_mul
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_padd
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

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (α : ℝ),
    (∀ j, j < r.length → ((i : ℤ) + j + 4) ∣ L) →
    pev (wsum L i r) α = (L : ℝ) * irow r i α := by
  intro r
  induction r with
  | nil => intro i α _; simp [irow]
  | cons p r ih =>
    intro i α hdvd
    have h0 : ((i : ℤ) + 4) ∣ L := by
      have := hdvd 0 (by simp)
      simpa using this
    obtain ⟨m, hm⟩ := h0
    have hine : ((i : ℤ) + 4) ≠ 0 := by positivity
    have hw : L / ((i : ℤ) + 4) = m := by rw [hm, Int.mul_ediv_cancel_left _ hine]
    have hcast : ((m : ℤ) : ℝ) * ((i : ℝ) + 4) = (L : ℝ) := by
      rw [hm]; push_cast; ring
    have hi4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have hrest : ∀ j, j < r.length → (((i + 1 : ℕ) : ℤ) + j + 4) ∣ L := by
      intro j hj
      have := hdvd (j + 1) (by simpa using Nat.succ_lt_succ hj)
      push_cast at this ⊢
      convert this using 2
      ring
    rw [wsum_cons, pev_padd, pev_map_mul, hw, ih (i + 1) α hrest]
    simp only [irow]
    field_simp
    linear_combination (pev p α) * hcast
end Sendov
