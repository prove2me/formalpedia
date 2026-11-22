-- Prove2me | solution 1 for TarskiQuasiFPT.UpperBound.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:32:09.328952+00:00
-- url     : https://prove2.me/submissions/61f4ef66-6753-47be-915d-93c57ddf4ca2

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false
open TarskiQuasiFPT.UpperBound

private theorem monotonic_bounds {n k : ℕ} [NeZero n] (Q Q' : QASet n k) (hQ : IsSafeQA Q) (hQ' : IsSafeQA Q')
    (hsub : QASubset Q Q') :
    ∀ s : Slice n k, Js Q s ≤ Js Q' s ∧ Ms Q' s ≤ Ms Q s := by
  classical
  intro s
  have restrict_consistency {h : Point n k → Point n k × Label} (hh : Consistent h Q') :
      Consistent h Q := fun x r hx => hh x r (hsub x r hx)
  constructor
  · apply Finset.sup_mono
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hy.1, fun h hm hc => hy.2 h hm (restrict_consistency hc)⟩
  · apply Finset.inf_mono
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨hy.1, fun h hm hc => hy.2 h hm (restrict_consistency hc)⟩

theorem solution {n k : ℕ} [NeZero n] (Q Q' : QASet n k) (hQ : IsSafeQA Q) (hQ' : IsSafeQA Q')
    (hsub : QASubset Q Q') :
    Fix Q' ⊆ Fix Q ∧ FixMinus Q' ⊆ FixMinus Q ∧ FixPlus Q' ⊆ FixPlus Q := by
  classical
  have hfix : Fix Q' ⊆ Fix Q := by
    intro x hx
    simp only [_root_.TarskiQuasiFPT.UpperBound.Fix, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro s hs
    obtain ⟨hl, hr⟩ := hx s hs
    obtain ⟨hm1, hm2⟩ := monotonic_bounds Q Q' hQ hQ' hsub s
    exact ⟨hm1.trans hl, hr.trans hm2⟩
  refine ⟨hfix, ?_, ?_⟩
  · intro x hx
    simp only [FixMinus, Finset.mem_filter] at hx ⊢
    refine ⟨hfix hx.1, ?_⟩
    rintro ⟨y, r, hy, hyx, hr⟩
    exact hx.2 ⟨y, r, hsub y r hy, hyx, hr⟩
  · intro x hx
    simp only [FixPlus, Finset.mem_filter] at hx ⊢
    refine ⟨hfix hx.1, ?_⟩
    rintro ⟨y, r, hy, hxy, hr⟩
    exact hx.2 ⟨y, r, hsub y r hy, hxy, hr⟩
#print axioms solution
