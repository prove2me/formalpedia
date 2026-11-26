-- Prove2me | solution 1 for card_valid_bases_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:59.091361+00:00
-- url     : https://prove2.me/submissions/b585135d-b237-4be1-9f06-78ae8efca9bd

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_valid_bases_bounds
import Theorems.Thm_two_pow_poly_le

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (hN : 10 ≤ Fintype.card α) :
    Fintype.card (ValidBasis α) ≤
      2 * 2 ^ (2 ^ Fintype.card α - Fintype.card α) := by
  have h2 : 2 ≤ Fintype.card α := le_trans (by decide : 2 ≤ 10) hN
  obtain ⟨_, hhi⟩ := card_valid_bases_bounds h2
  refine hhi.trans ?_
  set N := Fintype.card α
  have hgap : N * (N - 1) + 3 * 2 ^ (N - 2) ≤ 2 ^ N - N := by
    have hpoly := two_pow_poly_le N hN
    have hsq : N * (N - 1) + N = N ^ 2 := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_self N), sq]
    have : N * (N - 1) + 3 * 2 ^ (N - 2) + N ≤ 2 ^ (N - 2) + 3 * 2 ^ (N - 2) := by
      linarith [hsq]
    have hsum : 2 ^ (N - 2) + 3 * 2 ^ (N - 2) = 4 * 2 ^ (N - 2) := by
      ring
    have h4 : 4 * 2 ^ (N - 2) = 2 ^ N := by
      have : 2 ≤ N := h2
      have hfour : (4 : ℕ) = 2 ^ 2 := by decide
      rw [hfour, ← pow_add, show 2 + (N - 2) = N by omega]
    exact Nat.le_sub_of_add_le (this.trans_eq (hsum.trans h4))
  have herr : 2 ^ (N * (N - 1) + 3 * 2 ^ (N - 2)) ≤ 2 ^ (2 ^ N - N) :=
    Nat.pow_le_pow_right (by decide) hgap
  have : 2 ^ (2 ^ N - N) + 2 ^ (N * (N - 1) + 3 * 2 ^ (N - 2)) ≤
      2 ^ (2 ^ N - N) + 2 ^ (2 ^ N - N) :=
    Nat.add_le_add_left herr _
  have h2D : 2 ^ (2 ^ N - N) + 2 ^ (2 ^ N - N) = 2 * 2 ^ (2 ^ N - N) := by
    rw [two_mul]
  exact this.trans_eq h2D
