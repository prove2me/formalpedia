-- Prove2me | solution 1 for SluggishCapability.Myopic.myopic_best_response
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:33:58.204986+00:00
-- url     : https://prove2.me/submissions/1b13c23d-5997-4fb3-a764-a79d093311c2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace Aux_SC_MBR
open SluggishCapability.Myopic

lemma inc (c : ℝ) (n d : ℕ) :
    periodCost c (n + 1) d = periodCost c n d + (if n < d then c - 1 else c) := by
  unfold periodCost
  push_cast
  split_ifs with h
  · have h' : (n : ℝ) + 1 ≤ d := by exact_mod_cast h
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · have h' : (d : ℝ) ≤ n := by exact_mod_cast (not_lt.mp h)
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring

end Aux_SC_MBR

open SluggishCapability.Myopic Aux_SC_MBR in
theorem solution (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (m d : ℕ) :
    (myopicStep m d + 1 = m ∨ myopicStep m d = m ∨ myopicStep m d = m + 1) ∧
    ∀ m' : ℕ, (m' + 1 = m ∨ m' = m ∨ m' = m + 1) → m' ≠ myopicStep m d →
      periodCost c (myopicStep m d) d < periodCost c m' d := by
  refine ⟨by unfold myopicStep; split_ifs <;> omega, ?_⟩
  intro m' hm' hne
  have hI := inc c
  by_cases h1 : m < d
  · have hs : myopicStep m d = m + 1 := by unfold myopicStep; rw [if_pos h1]
    rw [hs] at hne ⊢
    rcases hm' with h | h | h
    · subst h
      rw [hI (m' + 1) d, hI m' d, if_pos h1, if_pos (by omega : m' < d)]
      linarith
    · subst h
      rw [hI m' d, if_pos h1]
      linarith
    · exact absurd h hne
  · by_cases h2 : d = m
    · have hs : myopicStep m d = m := by unfold myopicStep; rw [if_neg h1, if_pos h2]
      rw [hs] at hne ⊢
      rcases hm' with h | h | h
      · subst h
        rw [hI m' d, if_pos (by omega : m' < d)]
        linarith
      · exact absurd h hne
      · subst h
        rw [hI m d, if_neg h1]
        linarith
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hs : myopicStep (k + 1) d = k := by
        unfold myopicStep; rw [if_neg h1, if_neg h2]; omega
      rw [hs] at hne ⊢
      rcases hm' with h | h | h
      · exact absurd (by omega : m' = k) hne
      · subst h
        rw [hI k d, if_neg (by omega : ¬ k < d)]
        linarith
      · subst h
        rw [hI (k + 1) d, hI k d, if_neg (by omega : ¬ k + 1 < d), if_neg (by omega : ¬ k < d)]
        linarith
