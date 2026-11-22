-- Prove2me | solution 1 for TarskiQuasiFPT.UpperBound.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:23:35.872866+00:00
-- url     : https://prove2.me/submissions/ae5b9400-d059-428e-83ef-b819f42f66a3

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false
open TarskiQuasiFPT.UpperBound

theorem solution {n k : ℕ} [NeZero n] (Q Q' : QASet n k) (hQ : IsSafeQA Q) (hQ' : IsSafeQA Q')
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
