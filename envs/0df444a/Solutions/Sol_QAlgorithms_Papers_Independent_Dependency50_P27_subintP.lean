-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.subintP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:22:59.054128+00:00
-- url     : https://prove2.me/submissions/82dc7780-9aa2-409e-86ca-f80ccae48c2b

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial


theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (i2 i1 : QAlgorithms.Papers.Independent.Dependency50.P27.Interval R)
    (h : subint i1 i2 = true) :
    ∀ x, intervalMem i1 x → intervalMem i2 x := by
  intro x hx
  obtain ⟨l1, u1⟩ := i1
  obtain ⟨l2, u2⟩ := i2
  simp only [subint, Bool.and_eq_true] at h
  obtain ⟨hl, hu⟩ := h
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · clear hu hx2
    rcases l1 with ⟨c1, v1⟩ | _ <;> rcases l2 with ⟨c2, v2⟩ | _ <;>
      simp only [lowerFits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hl ⊢ hx1
    all_goals first
      | trivial
      | (cases c1 <;> cases c2 <;> simp at hx1 hl ⊢ <;> first | order | (rcases hl with hl | hl <;> order))
  · clear hl hx1
    rcases u1 with ⟨c1, v1⟩ | _ <;> rcases u2 with ⟨c2, v2⟩ | _ <;>
      simp only [upperFits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hu ⊢ hx2
    all_goals first
      | trivial
      | (cases c1 <;> cases c2 <;> simp at hx2 hu ⊢ <;> first | order | (rcases hu with hu | hu <;> order))

end
