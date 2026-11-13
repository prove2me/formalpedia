-- Prove2me | solution 1 for TangleStructTree.closure_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:18.89598+00:00
-- url     : https://prove2.me/submissions/a36ce056-0c7a-45be-92db-63fb122ed9c9

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

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.ClosureEq

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma requires_iff (σ : Set E) (hσ : IsConsistent σ) (x : E) (hx : x ∉ σ) :
    Requires σ x ↔ ∃ r ∈ σ, (r ≠ x ∧ r ≠ rev x) ∧ r < x := by
  constructor
  · rintro ⟨-, hinc⟩
    unfold IsConsistent at hinc
    push_neg at hinc
    obtain ⟨a, ha, b, hb, hba, hbra, hab⟩ := hinc
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hba
      · -- a = rev x, b ∈ σ : rev x ≤ rev b
        have h1 : b ≤ x := by
          have := SepSystem.rev_le_rev _ _ hab
          simpa only [rev_rev] using this
        refine ⟨b, hb, ⟨?_, ?_⟩, lt_of_le_of_ne h1 ?_⟩
        · rintro rfl; exact hx hb
        · exact hba
        · rintro rfl; exact hx hb
    · rcases hb with rfl | hb
      · -- b = rev x, a ∈ σ, a ≤ rev b = x
        have h1 : a ≤ x := by simpa [rev_rev] using hab
        refine ⟨a, ha, ⟨?_, ?_⟩, lt_of_le_of_ne h1 ?_⟩
        · rintro rfl; exact hx ha
        · exact fun h => hba h.symm
        · rintro rfl; exact hx ha
      · exact absurd hab (hσ a ha b hb hba hbra)
  · rintro ⟨r, hr, ⟨h1, h2⟩, hlt⟩
    refine ⟨hx, fun hc => ?_⟩
    have := hc r (Set.mem_insert_of_mem _ hr) (rev x) (Set.mem_insert _ _)
      (fun h => h2 h.symm) (fun h => h1 (by have := congrArg rev h; simpa [rev_rev] using this.symm)) 
    exact this (by simpa [rev_rev] using hlt.le)

end TangleStructTree.Dev.ClosureEq

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.ClosureEq

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_closure_eq (σ : Set E) (hσ : IsConsistent σ) :
    (∀ x : E, x ∉ σ → (Requires σ x ↔ ∃ r ∈ σ, (r ≠ x ∧ r ≠ rev x) ∧ r < x)) ∧
      sepClosure σ = σ ∪ {x | ∃ r ∈ σ, (r ≠ x ∧ r ≠ rev x) ∧ r < x} := by
  refine ⟨fun x hx => requires_iff σ hσ x hx, ?_⟩
  ext x
  simp only [sepClosure, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hx : x ∈ σ
      · exact Or.inl hx
      · exact Or.inr ((requires_iff σ hσ x hx).mp h)
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hx : x ∈ σ
      · exact Or.inl hx
      · exact Or.inr ((requires_iff σ hσ x hx).mpr h)

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_closure_eq := @TangleStructTree.chk_closure_eq
