-- Prove2me | solution 1 for Sendov.unpackZ_pevZ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:24.099163+00:00
-- url     : https://prove2.me/submissions/88ac1f54-f692-451c-b734-30f69082331b

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
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_bdig_add_mul
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
theorem _root_.solution (β : ℤ) (hβ : 0 < β) :
    ∀ (m : ℕ) (p : List ℤ), p.length ≤ m → (∀ a ∈ p, 2 * |a| < β) →
      unpackZ β m (pevZ p β) = p ++ List.replicate (m - p.length) 0 := by
  intro m
  induction m with
  | zero =>
    intro p hlen _
    simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)]
  | succ m ih =>
    intro p hlen hb
    cases p with
    | nil =>
      have h0 : bdig β 0 = 0 := by
        have : (0 : ℤ) % β = 0 := Int.zero_emod β
        simp only [bdig, this]
        split_ifs <;> omega
      simp only [pevZ_nil, unpackZ_succ, h0, List.nil_append, List.length_nil,
        Nat.sub_zero, List.replicate_succ]
      have := ih [] (Nat.zero_le m) (by simp)
      simpa using this
    | cons a p =>
      have ha : 2 * |a| < β := hb a (List.mem_cons_self ..)
      have hp : ∀ x ∈ p, 2 * |x| < β := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      have hd : bdig β (a + β * pevZ p β) = a := bdig_add_mul β a _ hβ ha
      have hq : (a + β * pevZ p β - a) / β = pevZ p β := by
        rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hβ.ne']
      simp only [pevZ_cons, unpackZ_succ, hd, hq, List.length_cons]
      rw [ih p (by simpa using Nat.le_of_succ_le_succ hlen) hp]
      simp
end Sendov
