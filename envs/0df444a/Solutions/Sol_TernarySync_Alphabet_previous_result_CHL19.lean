-- Prove2me | solution 1 for TernarySync.Alphabet.previous_result_CHL19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:13.571946+00:00
-- url     : https://prove2.me/submissions/1774d92d-f5db-41ab-bb36-fe06ec466739

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString
import Theorems.Thm_TernarySync_Alphabet_sync_square_free

section
set_option autoImplicit false

namespace TernarySync.Dev.CHL19
open TernarySync.Alphabet

theorem four_fin2 : ∀ a b c d : Fin 2, a = b ∨ b = c ∨ c = d ∨ (a = c ∧ b = d) := by decide

theorem not_sqfree_four (l : List (Fin 2)) (hl : l.length = 4) : ¬ IsSquareFree l := by
  match l, hl with
  | [a, b, c, d], _ =>
    intro h
    rcases four_fin2 a b c d with h1 | h1 | h1 | ⟨h1, h2⟩
    · subst h1
      exact h [a, a] ⟨[], [c, d], by simp⟩ ⟨[a], by simp, rfl⟩
    · subst h1
      exact h [b, b] ⟨[a], [d], by simp⟩ ⟨[b], by simp, rfl⟩
    · subst h1
      exact h [c, c] ⟨[a, b], [], by simp⟩ ⟨[c], by simp, rfl⟩
    · subst h1 h2
      exact h [a, b, a, b] ⟨[], [], by simp⟩ ⟨[a, b], by simp, rfl⟩

end TernarySync.Dev.CHL19

namespace TernarySync.Alphabet
open TernarySync.Dev.CHL19 in
theorem chk_previous_result_CHL19 (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ M : ℕ, ∀ S : List (Fin 2), IsSyncString ε S → S.length ≤ M := by
  refine ⟨3, fun S hS => ?_⟩
  by_contra hlen
  have hsf := (TernarySync.Alphabet.sync_square_free ε hε0 hε1 S).1 hS
  have hpre := (TernarySync.Alphabet.sync_square_free ε hε0 hε1 S).2.2 (S.take 4)
    (List.take_prefix 4 S).isInfix hsf
  exact not_sqfree_four _ (by simp; omega) hpre
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_previous_result_CHL19 := @TernarySync.Alphabet.chk_previous_result_CHL19
