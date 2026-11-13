-- Prove2me | solution 1 for TernarySync.Alphabet.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:33:57.168833+00:00
-- url     : https://prove2.me/submissions/c78e53a1-d4a1-4d88-a70e-a7732089ca79

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString
import Theorems.Thm_TernarySync_Alphabet_theorem_4_1
import Theorems.Thm_TernarySync_Alphabet_sync_square_free
import Theorems.Thm_TernarySync_Alphabet_previous_result_CHL19

section
set_option autoImplicit false

namespace TernarySync.Alphabet
theorem chk_theorem_1_2 :
    (∀ n : ℕ, 1 ≤ n → ∃ S : List (Fin 3), S.length = n ∧ IsSyncString ((2001 : ℝ) / 2002) S) ∧
      IsLeast {q : ℕ | ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∃ S : List (Fin q), S.length = n ∧ IsSyncString ε S} 3 := by
  refine ⟨fun n hn => theorem_4_1 n hn, ⟨⟨(2001 : ℝ) / 2002, by norm_num, by norm_num,
    fun n hn => theorem_4_1 n hn⟩, ?_⟩⟩
  rintro q ⟨ε, h0, h1, h⟩
  by_contra hq
  push_neg at hq
  interval_cases q
  · obtain ⟨S, hS, -⟩ := h 1 le_rfl
    match S, hS with
    | [a], _ => exact a.elim0
  · obtain ⟨S, hS, hsy⟩ := h 2 (by norm_num)
    have hsf := (sync_square_free ε h0 h1 S).1 hsy
    match S, hS with
    | [a, b], _ =>
      have hab : a = b := Subsingleton.elim _ _
      subst hab
      exact hsf [a, a] (List.infix_refl _) ⟨[a], by simp, rfl⟩
  · obtain ⟨M, hM⟩ := previous_result_CHL19 ε h0 h1
    obtain ⟨S, hS, hsy⟩ := h (M + 1) (by omega)
    have := hM S hsy
    omega
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_theorem_1_2 := @TernarySync.Alphabet.chk_theorem_1_2
