-- Prove2me | solution 1 for card_valid_bases_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:44.780679+00:00
-- url     : https://prove2.me/submissions/d1b8280b-204f-4fff-9cc7-ad2aa87c7c3e

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_valid_bases_ge_discrete
import Theorems.Thm_card_valid_bases_ratio_le_one_add_half_pow

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
open Filter Topology
omit [Fintype α] [DecidableEq α]
theorem _root_.solution :
    Tendsto (fun n : ℕ =>
      (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n))
      atTop (nhds (1 : ℝ)) := by
  have hge : ∀ n,
      1 ≤ (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n) := by
    intro n
    refine (one_le_div (pow_pos (by norm_num : (0 : ℝ) < 2) (2 ^ n - n))).mpr ?_
    have h := card_valid_bases_ge_discrete (α := Fin n)
    have := (Nat.cast_le (α := ℝ)).mpr (by simpa using h)
    simpa [Nat.cast_pow] using this
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hupper : Tendsto (fun n : ℕ => (1 : ℝ) + (1 / 2 : ℝ) ^ n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) hupper
    (Eventually.of_forall hge)
    (eventually_atTop.2 ⟨10, fun n hn => card_valid_bases_ratio_le_one_add_half_pow n hn⟩)
