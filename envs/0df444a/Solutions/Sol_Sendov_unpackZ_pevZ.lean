-- Prove2me | solution 1 for Sendov.unpackZ_pevZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:14.610695+00:00
-- url     : https://prove2.me/submissions/1c484ea4-3b92-4fc5-a15e-bab1fbddfc1a

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
import Theorems.Thm_Sendov_bdig_add_mul
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
theorem _root_.solution (b : ℤ) (hb : 0 < b) :
    ∀ p : List ℤ, (∀ a ∈ p, 2 * |a| < b) → unpackZ b p.length (pevZ p b) = p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a p ih =>
    intro hlt
    have ha : 2 * |a| < b := hlt a (List.mem_cons_self ..)
    have hp : ∀ x ∈ p, 2 * |x| < b := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hd : bdig b (a + b * pevZ p b) = a := bdig_add_mul b a _ hb ha
    have hq : (a + b * pevZ p b - a) / b = pevZ p b := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hb.ne']
    simp only [List.length_cons, pevZ_cons, unpackZ_succ, hd, hq, ih hp]
end Sendov
