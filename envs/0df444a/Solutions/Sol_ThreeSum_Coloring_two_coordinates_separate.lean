-- Prove2me | solution 1 for ThreeSum.Coloring.two_coordinates_separate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:27.654984+00:00
-- url     : https://prove2.me/submissions/5599eb0b-6581-4f59-87c9-5c5fa660aa25

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}

private theorem exists_coordinate_ne {s t : α → Bool} (h : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra hn
  push Not at hn
  exact h (funext hn)

/-- Two coordinates suffice to distinguish any three different binary words. -/
theorem two_coordinates_separate_sourceProof {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ i j, (s i, s j) ≠ (t i, t j) ∧
      (s i, s j) ≠ (u i, u j) ∧ (t i, t j) ≠ (u i, u j) := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have hui : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hui with hui | hui
  · obtain ⟨j, hj⟩ := exists_coordinate_ne hsu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · exact fun he => hj (congrArg Prod.snd he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui).symm
  · obtain ⟨j, hj⟩ := exists_coordinate_ne htu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui)
    · exact fun he => hj (congrArg Prod.snd he)



































































































































































end ThreeSum.Coloring

end

universe u_1

theorem solution : ∀ {α : Type u_1} {s t u : α → Bool},
  @Ne.{u_1 + 1} (α → Bool) s t →
    @Ne.{u_1 + 1} (α → Bool) s u →
      @Ne.{u_1 + 1} (α → Bool) t u →
        ∃ (i : α) (j : α),
          And
            (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j))
              (@Prod.mk.{0, 0} Bool Bool (t i) (t j)))
            (And
              (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j))
                (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))
              (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (t i) (t j))
                (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))) := by
  exact @ThreeSum.Coloring.two_coordinates_separate_sourceProof

#print axioms solution
