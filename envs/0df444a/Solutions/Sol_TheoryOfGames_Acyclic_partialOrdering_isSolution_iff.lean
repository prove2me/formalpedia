-- Prove2me | solution 1 for TheoryOfGames.Acyclic.partialOrdering_isSolution_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:49:54.195805+00:00
-- url     : https://prove2.me/submissions/14cbfcaf-a1fe-46a8-a8f1-bf6d0795b196

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_PartialOrdering

set_option autoImplicit false

open TheoryOfGames.Acyclic in
theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hS : IsPartialOrdering D S) (V : Set α) :
    IsSolution D S V ↔ ConditionG D S ∧ V = maxima D S := by
  have htr := hS.2
  constructor
  · intro hV
    unfold IsSolution at hV
    have hVD : V ⊆ D := by
      intro v hv
      rw [hV] at hv
      exact hv.1
    have hEq : V = maxima D S := by
      ext v
      constructor
      · intro hv
        have hv' := hv
        rw [hV] at hv'
        refine ⟨hv'.1, ?_⟩
        intro y hy hyv
        by_cases hyV : y ∈ V
        · exact hv'.2 y hyV hyv
        · have hnot : ¬ (y ∈ D ∧ ∀ x ∈ V, ¬ S x y) := by
            intro h
            apply hyV
            rw [hV]
            exact h
          push_neg at hnot
          obtain ⟨x, hxV, hxy⟩ := hnot hy
          exact hv'.2 x hxV (htr x (hVD hxV) y hy v hv'.1 hxy hyv)
      · intro hm
        rw [hV]
        exact ⟨hm.1, fun x hx => hm.2 x (hVD hx)⟩
    refine ⟨?_, hEq⟩
    intro y hy hnm
    have hyV : y ∉ V := by
      rw [hEq]
      exact hnm
    have hnot : ¬ (y ∈ D ∧ ∀ x ∈ V, ¬ S x y) := by
      intro h
      apply hyV
      rw [hV]
      exact h
    push_neg at hnot
    obtain ⟨x, hxV, hxy⟩ := hnot hy
    exact ⟨x, hEq ▸ hxV, hxy⟩
  · rintro ⟨hG, hEq⟩
    subst hEq
    unfold IsSolution
    ext y
    constructor
    · intro hm
      exact ⟨hm.1, fun x hx => hm.2 x hx.1⟩
    · rintro ⟨hy, hno⟩
      by_contra hnm
      obtain ⟨x, hx, hxy⟩ := hG y hy hnm
      exact hno x hx hxy
