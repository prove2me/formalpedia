-- Prove2me | solution 1 for Sendov.unpackN_npev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:31.22556+00:00
-- url     : https://prove2.me/submissions/cb6d96b6-fba6-4ec1-a44b-acb192875a46

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackN_succ
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackN_succ

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b : ℕ) (hb : 0 < b) :
    ∀ p : List ℕ, (∀ a ∈ p, a < b) → unpackN b p.length (npev p b) = p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a p ih =>
    intro hlt
    have ha : a < b := hlt a (List.mem_cons_self ..)
    have hp : ∀ x ∈ p, x < b := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hmod : (a + b * npev p b) % b = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have hdiv : (a + b * npev p b) / b = npev p b := by
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
    simp only [List.length_cons, npev_cons, unpackN_succ, hmod, hdiv, ih hp]
end Sendov
