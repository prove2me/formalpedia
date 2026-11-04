-- Prove2me | solution 1 for ThreeSum.Cover.exists_good_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:12.34421+00:00
-- url     : https://prove2.me/submissions/6bddb3e6-d526-441f-82ee-77c4030ba7f8

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover
import Theorems.Thm_ThreeSum_Cover_incidence_card_sum

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
namespace ThreeSum.Cover
theorem _root_.solution {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq U] (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] (a : ℕ)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∃ ω, targets.card ≤ a * (targets.filter (covers ω)).card := by
  by_contra! hnone
  have hlow := sum_le_sum hfrequency
  have hhigh : (∑ ω, a * (targets.filter (covers ω)).card) <
      ∑ _ω : Ω, targets.card := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using hnone)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum] at hlow hhigh
  rw [incidence_card_sum targets covers] at hhigh
  nlinarith
end ThreeSum.Cover
