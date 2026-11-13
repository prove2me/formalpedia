-- Prove2me | solution 1 for TangleStructTree.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:19.809218+00:00
-- url     : https://prove2.me/submissions/125d5602-a74f-4485-bf41-3f10a650f61d

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma consistent_mono {σ τ : Set E} (h : σ ⊆ τ) (hτ : IsConsistent τ) : IsConsistent σ :=
  fun x hx y hy => hτ x (h hx) y (h hy)

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_2_1 (σ τ : Set E) (hστ : σ ⊆ τ) (hσ : IsConsistent σ) (hτ : IsConsistent τ) :
    sepClosure σ ⊆ sepClosure τ ∧ (IsOrientation τ → sepClosure τ = τ) := by
  constructor
  · intro x hx
    rcases hx with hx | ⟨hxσ, hinc⟩
    · exact Or.inl (hστ hx)
    · by_cases hxτ : x ∈ τ
      · exact Or.inl hxτ
      · exact Or.inr ⟨hxτ, fun hc => hinc (consistent_mono (Set.insert_subset_insert hστ) hc)⟩
  · intro hor
    ext x
    constructor
    · rintro (h | ⟨hxτ, hinc⟩)
      · exact h
      · rcases (hor x).1 with h | h
        · exact absurd h hxτ
        · exact absurd (by rw [Set.insert_eq_of_mem h]; exact hτ) hinc
    · intro h; exact Or.inl h

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_2_1 := @TangleStructTree.chk_lemma_2_1
