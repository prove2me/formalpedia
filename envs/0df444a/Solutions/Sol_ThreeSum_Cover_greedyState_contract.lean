-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:35.761383+00:00
-- url     : https://prove2.me/submissions/bbeb65bf-71d3-4aaa-90ff-acb397d588fe

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy
import Theorems.Thm_ThreeSum_Cover_selectMap_max
import Theorems.Thm_ThreeSum_Cover_greedyState_subset
import Theorems.Thm_ThreeSum_Cover_exists_good_cover
import Theorems.Thm_ThreeSum_Cover_survivor_step


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
    a * (greedyState maps covers targets (t + 1)).card ≤
      (a - 1) * (greedyState maps covers targets t).card := by
  let old := greedyState maps covers targets t
  have hfreq : ∀ u ∈ old,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card := by
    intro u hu
    exact hfrequency u (greedyState_subset maps covers targets t hu)
  obtain ⟨ω, hω⟩ := exists_good_cover old covers a hfreq
  have hbest := selectMap_max maps covers old (hall ω)
  exact survivor_step old (covers (selectMap maps covers old)) a ha
    (hω.trans (Nat.mul_le_mul_left a hbest))
end ThreeSum.Cover
