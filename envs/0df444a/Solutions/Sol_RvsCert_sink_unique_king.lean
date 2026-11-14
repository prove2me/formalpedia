-- Prove2me | solution 1 for RvsCert.sink_unique_king
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T09:32:41.097514+00:00
-- url     : https://prove2.me/submissions/3a7b0744-ae2e-4e60-b7bf-f24212d483c3

import Mathlib.Order.Basic
import Definitions.Def_RvsCert_IsSink
import Definitions.Def_RvsCert_IsKing

open RvsCert

theorem solution (m : ℕ) (x : TPair m → Bool) (s : Fin m) (hs : IsSink x s) :
    IsKing x s ∧ ∀ v : Fin m, IsKing x v → v = s := by
  -- No vertex beats itself.
  have irrefl : ∀ a : Fin m, ¬ beats x a a := by
    intro a h
    simp [beats] at h
  -- The relation `beats` is asymmetric.
  have asymm : ∀ a b : Fin m, beats x a b → ¬ beats x b a := by
    intro a b hab hba
    rcases lt_trichotomy a b with h | h | h
    · rw [beats, dif_pos h] at hab
      rw [beats, dif_neg (not_lt.mpr h.le), dif_pos h] at hba
      rw [hab] at hba
      exact Bool.noConfusion hba
    · subst h
      exact irrefl a hab
    · rw [beats, dif_neg (not_lt.mpr h.le), dif_pos h] at hab
      rw [beats, dif_pos h] at hba
      rw [hba] at hab
      exact Bool.noConfusion hab
  refine ⟨fun u hu => Or.inl (hs u hu), fun v hv => ?_⟩
  by_contra hvs
  rcases hv s (Ne.symm hvs) with h | ⟨w, hvw, hws⟩
  · exact asymm s v (hs v hvs) h
  · by_cases hw : w = s
    · rw [hw] at hws
      exact irrefl s hws
    · exact asymm s w (hs w hw) hws
