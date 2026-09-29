-- Prove2me | solution 1 for RobustMeanCov.TwoPoint.lemma1Quad_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:28.580894+00:00
-- url     : https://prove2.me/submissions/54326968-8930-4b30-8f78-ca06aed6ffa0

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

open RobustMeanCov.TwoPoint

theorem solution (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b) :
    deriv (lemma1Quad u a b qa qb) a = qa ∧ deriv (lemma1Quad u a b qa qb) b = qb := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hfun : lemma1Quad u a b qa qb = fun y : ℝ =>
      lemma1A a b qa qb * y ^ 2 + lemma1B a b qa qb * y + lemma1C u a b qa qb := rfl
  have key : ∀ y : ℝ, HasDerivAt (lemma1Quad u a b qa qb)
      (2 * lemma1A a b qa qb * y + lemma1B a b qa qb) y := by
    intro y
    rw [hfun]
    have h2 : HasDerivAt (fun z : ℝ => lemma1A a b qa qb * z ^ 2)
        (lemma1A a b qa qb * ((2 : ℕ) * y ^ (2 - 1))) y := (hasDerivAt_pow 2 y).const_mul _
    have h3 : HasDerivAt (fun z : ℝ => lemma1B a b qa qb * z)
        (lemma1B a b qa qb * 1) y := (hasDerivAt_id y).const_mul _
    have h4 := (h2.add h3).add_const (lemma1C u a b qa qb)
    have heq : lemma1A a b qa qb * ((2 : ℕ) * y ^ (2 - 1)) + lemma1B a b qa qb * 1
        = 2 * lemma1A a b qa qb * y + lemma1B a b qa qb := by push_cast; ring
    rw [← heq]
    exact h4
  refine ⟨?_, ?_⟩
  · rw [(key a).deriv]
    simp only [lemma1A, lemma1B]
    field_simp
    ring
  · rw [(key b).deriv]
    simp only [lemma1A, lemma1B]
    field_simp
    ring
