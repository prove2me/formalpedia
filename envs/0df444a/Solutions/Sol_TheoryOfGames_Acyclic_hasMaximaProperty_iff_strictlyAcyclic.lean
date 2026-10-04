-- Prove2me | solution 1 for TheoryOfGames.Acyclic.hasMaximaProperty_iff_strictlyAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:29:29.309389+00:00
-- url     : https://prove2.me/submissions/e4825b3a-5bb6-4b3f-9e80-f8ed6ca2b2e9

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

set_option autoImplicit false

open TheoryOfGames.Acyclic in
theorem solution {α : Type*} (D : Set α) (S : α → α → Prop) :
    HasMaximaProperty D S ↔ IsStrictlyAcyclic D S := by
  constructor
  · rintro h ⟨x, hxD, hxS⟩
    obtain ⟨y, hyE, hy⟩ := h (Set.range x) (by rintro _ ⟨i, rfl⟩; exact hxD i) ⟨x 0, 0, rfl⟩
    obtain ⟨i, rfl⟩ := hyE
    exact hy (x (i + 1)) ⟨i + 1, rfl⟩ (hxS i)
  · intro h E hED hE
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have key : ∀ a : E, ∃ b : E, S b.1 a.1 := by
      intro a
      by_contra hc
      push_neg at hc
      have hm : a.1 ∈ maxima E S := ⟨a.2, fun y hy => hc ⟨y, hy⟩⟩
      rw [hne] at hm
      exact hm
    choose f hf using key
    obtain ⟨e, he⟩ := hE
    apply h
    refine ⟨fun n => (f^[n] ⟨e, he⟩).1, fun i => hED (f^[i] ⟨e, he⟩).2, fun i => ?_⟩
    simp only [Function.iterate_succ_apply']
    exact hf _
