-- Prove2me | solution 1 for TangleStructTree.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:19.296886+00:00
-- url     : https://prove2.me/submissions/4b4d6b8e-ecda-41ff-943d-69aaeafefa83

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_IsTrivial
import Theorems.Thm_TangleStructTree_closure_eq

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma rev_lt_rev {x y : E} (h : x < y) : rev y < rev x := by
  refine lt_of_le_of_ne (SepSystem.rev_le_rev _ _ h.le) ?_
  intro h'
  have := congrArg rev h'
  rw [rev_rev, rev_rev] at this
  exact h.ne this.symm

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.L22

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_cl (τ : Set E) (hτ : IsConsistent τ) {x : E} :
    x ∈ sepClosure τ ↔ x ∈ τ ∨ ∃ r ∈ τ, (r ≠ x ∧ r ≠ rev x) ∧ r < x := by
  rw [(TangleStructTree.closure_eq τ hτ).2]
  simp [Set.mem_union]

lemma trivial_of {a r : E} (h1 : r < rev a) (h2 : rev r < rev a) : IsTrivial (rev a) := ⟨r, h1, h2⟩

/-- consistency applied to a pair `t1 ≤ rev t2` in `τ`. -/
lemma pair_eq (τ : Set E) (hτ : IsConsistent τ) {t1 t2 : E} (h1 : t1 ∈ τ) (h2 : t2 ∈ τ)
    (h : t1 ≤ rev t2) : t2 = t1 ∨ t2 = rev t1 := by
  by_contra hc
  push_neg at hc
  exact hτ t1 h1 t2 h2 hc.1 hc.2 h

end TangleStructTree.Dev.L22

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.L22

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_2_2 (τ : Set E) (hτ : IsConsistent τ) (hco : ∀ x ∈ τ, ¬ IsTrivial (rev x)) :
    IsConsistent (sepClosure τ) ∧
      ∀ x : E, x ∈ sepClosure τ \ τ → rev x ∈ sepClosure τ \ τ → rev x = x := by
  constructor
  · intro a ha b hb hba hbra hab
    have hab' : b ≤ rev a := by
      have := SepSystem.rev_le_rev _ _ hab
      simpa [rev_rev] using this
    rcases (mem_cl τ hτ).mp ha with ha | ⟨t, ht, ⟨hta, htra⟩, hlt⟩ <;>
      rcases (mem_cl τ hτ).mp hb with hb | ⟨u, hu, ⟨hub, hurb⟩, hlu⟩
    · exact hτ a ha b hb hba hbra hab
    · have h1 : a ≤ rev u := hab.trans (SepSystem.rev_le_rev _ _ hlu.le)
      rcases pair_eq τ hτ ha hu h1 with h | h
      · rw [h] at hlu
        refine hco a ha (trivial_of (r := rev b) (rev_lt_rev hlu) ?_)
        rw [rev_rev]; exact lt_of_le_of_ne hab' hbra
      · rw [h] at hlu
        have := rev_lt_rev hlu
        rw [rev_rev] at this
        exact lt_irrefl _ (lt_of_le_of_lt hab this)
    · have h1 : t ≤ rev b := hlt.le.trans hab
      rcases pair_eq τ hτ ht hb h1 with h | h
      · rw [← h] at hlt
        refine hco b hb (trivial_of (r := a) ?_ (rev_lt_rev hlt))
        refine lt_of_le_of_ne hab (fun h' => hbra ?_)
        rw [h', rev_rev]
      · rw [h, rev_rev] at hab
        exact lt_irrefl _ (lt_of_lt_of_le hlt hab)
    · have hr := SepSystem.rev_le_rev _ _ hlu.le
      have h1 : t ≤ rev u := hlt.le.trans (hab.trans hr)
      rcases pair_eq τ hτ ht hu h1 with h | h
      · rw [h] at hlu
        refine hco t ht (trivial_of (r := a) ?_ (rev_lt_rev hlt))
        exact lt_of_le_of_lt hab (rev_lt_rev hlu)
      · rw [h] at hlu
        have h2 := rev_lt_rev hlu
        rw [rev_rev] at h2
        exact lt_irrefl _ ((lt_of_lt_of_le hlt hab).trans h2)
  · rintro x ⟨hx, hxτ⟩ ⟨hrx, hrxτ⟩
    rcases (mem_cl τ hτ).mp hx with h | ⟨t, ht, ⟨-, -⟩, hlt⟩
    · exact absurd h hxτ
    rcases (mem_cl τ hτ).mp hrx with h | ⟨u, hu, ⟨-, -⟩, hlu⟩
    · exact absurd h hrxτ
    have h2 := rev_lt_rev hlu
    rw [rev_rev] at h2
    have h1 : t ≤ rev u := (hlt.trans h2).le
    rcases pair_eq τ hτ ht hu h1 with h | h
    · exfalso
      rw [h] at hlu
      refine hco t ht (trivial_of (r := x) ?_ (rev_lt_rev hlt))
      have := rev_lt_rev hlu
      rwa [rev_rev] at this
    · exfalso
      rw [h] at hlu
      have h3 := rev_lt_rev hlt
      exact lt_irrefl _ (hlu.trans h3)

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_2_2 := @TangleStructTree.chk_lemma_2_2
