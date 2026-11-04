-- Prove2me | solution 1 for ThreeSum.Cover.support_cauchy_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:12.391768+00:00
-- url     : https://prove2.me/submissions/15961e0e-7eca-4b5d-b79b-7e4d98e6f592

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

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
namespace ThreeSum.Cover
theorem _root_.solution {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    (∑ ω, f ω) ^ 2 ≤
      ((univ.filter fun ω => f ω ≠ 0).card : ℝ) * ∑ ω, (f ω) ^ 2 := by
  classical
  let s := univ.filter fun ω => f ω ≠ 0
  have hsum : ∑ ω ∈ s, f ω = ∑ ω, f ω := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have hsq : ∑ ω ∈ s, (f ω) ^ 2 = ∑ ω, (f ω) ^ 2 := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  rw [hsum, hsq] at h
  exact h
end ThreeSum.Cover
