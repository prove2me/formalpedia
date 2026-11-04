-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:41.106274+00:00
-- url     : https://prove2.me/submissions/706d3554-d45a-4283-9098-8fff6ce7b9af

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_WeightedCache3SUM_Alias_4a1108cc76218e61
import Theorems.Thm_ThreeSum_Cover_half_power_bound

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
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (k : ℕ) :
    2 ^ k * (greedyState maps covers targets (a * k)).card ≤ targets.card := by
  have ha0 : 0 < a := by omega
  have hgeom := greedyState_geometric maps hall covers targets a ha0 hfrequency (a * k)
  have hhalf := Nat.pow_le_pow_left (half_power_bound a ha0) k
  simp only [mul_pow, ← pow_mul] at hhalf
  have hpos : 0 < (a - 1) ^ (a * k) := Nat.pow_pos (by omega)
  have hm := Nat.mul_le_mul_right (greedyState maps covers targets (a * k)).card hhalf
  nlinarith
end ThreeSum.Cover
