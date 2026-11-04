-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_geometric_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:57.551768+00:00
-- url     : https://prove2.me/submissions/580f74af-13ad-4ed4-8315-de9387080d8a

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
import Theorems.Thm_ThreeSum_Cover_greedyState_contract

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.Cover
theorem _root_.solution [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a ^ t * (greedyState maps covers targets t).card ≤ (a - 1) ^ t * targets.card := by
  induction t with
  | zero => simp [greedyState]
  | succ t ih =>
    have hs := greedyState_contract maps hall covers targets a ha hfrequency t
    calc
      a ^ (t + 1) * (greedyState maps covers targets (t + 1)).card =
          a ^ t * (a * (greedyState maps covers targets (t + 1)).card) := by ring
      _ ≤ a ^ t * ((a - 1) * (greedyState maps covers targets t).card) :=
        Nat.mul_le_mul_left _ hs
      _ = (a - 1) * (a ^ t * (greedyState maps covers targets t).card) := by ring
      _ ≤ (a - 1) * ((a - 1) ^ t * targets.card) := Nat.mul_le_mul_left _ ih
      _ = (a - 1) ^ (t + 1) * targets.card := by ring
end ThreeSum.Cover
