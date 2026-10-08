-- Prove2me | solution 1 for RegretMatching.Approach.support_negOrthant
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:06:31.747643+00:00
-- url     : https://prove2.me/submissions/b0ae150f-f7dc-4ba1-8661-cb6683e66e07

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open RegretMatching.Approach

theorem solution
    {L : Type} [Fintype L] (lam : EuclideanSpace ℝ L) :
    ((∀ l, 0 ≤ lam l) → IsLUB ((fun c => inner ℝ lam c) '' negOrthant L) 0) ∧
      ((∃ l, lam l < 0) → ¬ BddAbove ((fun c => inner ℝ lam c) '' negOrthant L)) := by
  classical
  constructor
  · intro hl
    constructor
    · rintro z ⟨c, hc, rfl⟩
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg (hc l) (hl l)
    · intro b hb
      apply hb
      exact ⟨0, (by intro l; simp), by simp⟩
  · rintro ⟨l, hl⟩ ⟨b, hb⟩
    let c : EuclideanSpace ℝ L := WithLp.toLp 2 (fun k => if k = l then -(abs b + 1) / (-lam l) else 0)
    have hc : c ∈ negOrthant L := by
      intro k
      change (if k = l then -(abs b + 1) / (-lam l) else 0) ≤ 0
      split_ifs
      · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by linarith)
      · rfl
    have he : inner ℝ lam c = abs b + 1 := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      change (∑ k, (if k = l then -(abs b + 1) / (-lam l) else 0) * lam k) = _
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp [ne_of_lt hl]
    have hh := hb (Set.mem_image_of_mem (fun c => inner ℝ lam c) hc)
    rw [he] at hh
    linarith [le_abs_self b]

#print axioms solution
