-- Prove2me | solution 1 for ThreeSum.Cover.greedy_cover_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:04.215048+00:00
-- url     : https://prove2.me/submissions/1fb064a0-03b8-4851-a430-3397fce75d10

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
import Theorems.Thm_ThreeSum_Cover_greedyState_spec
import Theorems.Thm_ThreeSum_Cover_greedyState_blocks

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.Cover
theorem _root_.solution [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 1 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∀ u ∈ targets,
      ∃ ω ∈ greedyChoices maps covers targets (a * (Nat.log2 targets.card + 1)),
        covers ω u := by
  have hblocks := greedyState_blocks maps hall covers targets a ha hfrequency
    (Nat.log2 targets.card + 1)
  have hlog := Nat.lt_log2_self (n := targets.card)
  have hzero : (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card = 0 := by
    by_contra hn
    have hp : 1 ≤ (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (Nat.log2 targets.card + 1)) hp
    nlinarith
  intro u hu
  by_contra! hnone
  have hmem := (greedyState_spec maps covers targets _ u).mpr ⟨hu, hnone⟩
  simpa [card_eq_zero.mp hzero] using hmem
end ThreeSum.Cover
