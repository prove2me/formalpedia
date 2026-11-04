-- Prove2me | solution 1 for ThreeSum.Coloring.two_coordinates_separate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:10.806892+00:00
-- url     : https://prove2.me/submissions/8f82685b-4cd3-4b3c-b954-a7af40cc288e

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
namespace ThreeSum.Coloring
variable {α : Type*}
private theorem exists_coordinate_ne {s t : α → Bool} (h : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra hn
  push Not at hn
  exact h (funext hn)
end ThreeSum.Coloring
set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {s t u : α → Bool}
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
