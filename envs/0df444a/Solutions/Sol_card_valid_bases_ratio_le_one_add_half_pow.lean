-- Prove2me | solution 1 for card_valid_bases_ratio_le_one_add_half_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:50:57.573159+00:00
-- url     : https://prove2.me/submissions/ba95d4cf-9a56-43cf-a70d-c6df82ec1220

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_valid_bases_bounds
import Theorems.Thm_remainder_exp_add_n_le

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
open Filter Topology
theorem _root_.solution (n : ℕ) (hn : 10 ≤ n) :
    (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n) ≤
      1 + (1 / 2 : ℝ) ^ n := by
  have h2 : 2 ≤ n := le_trans (by decide : 2 ≤ 10) hn
  have hN : 2 ≤ Fintype.card (Fin n) := by simpa using h2
  obtain ⟨_, hbound⟩ := card_valid_bases_bounds (α := Fin n) hN
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n - n) := pow_pos (by norm_num) _
  have hC :
      (Fintype.card (ValidBasis (Fin n)) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - n) + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hbound
    simpa [Nat.cast_add, Nat.cast_pow, Fintype.card_fin] using this
  have hdiv := div_le_div_of_nonneg_right hC hDpos.le
  have hsplit :
      ((2 : ℝ) ^ (2 ^ n - n) + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2))) /
          (2 : ℝ) ^ (2 ^ n - n) =
        1 + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2)) / (2 : ℝ) ^ (2 ^ n - n) := by
    field_simp [hDpos.ne']
  refine hdiv.trans ((le_of_eq hsplit).trans (add_le_add le_rfl ?_))
  set a := n * (n - 1) + 3 * 2 ^ (n - 2)
  set b := 2 ^ n - n
  have hab : a + n ≤ b := remainder_exp_add_n_le n hn
  have hmon :
      (2 : ℝ) ^ a / (2 : ℝ) ^ b ≤ (2 : ℝ) ^ a / (2 : ℝ) ^ (a + n) :=
    div_le_div_of_nonneg_left (pow_nonneg (by norm_num) _)
      (pow_pos (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hab)
  have hsimp : (2 : ℝ) ^ a / (2 : ℝ) ^ (a + n) = (1 / 2 : ℝ) ^ n := by
    rw [pow_add (2 : ℝ) a n, div_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      one_div, inv_pow]
  exact hmon.trans_eq hsimp
