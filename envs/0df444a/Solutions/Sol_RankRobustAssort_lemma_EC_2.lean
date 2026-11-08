-- Prove2me | solution 1 for RankRobustAssort.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:07:01.346072+00:00
-- url     : https://prove2.me/submissions/4c63eb8d-085d-42d6-9bfb-12987af7f448

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Reach

open RankRobustAssort in
theorem solution {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (ht : InL P t)
    (i j : Fin (n + 1)) (h : Reach P t j i) :
    ∃ m, j = t m := by
  unfold Reach at h
  cases h with
  | single he =>
    obtain ⟨m, _, _, hm⟩ := he
    exact ⟨m, hm⟩
  | tail _ he =>
    obtain ⟨m, _, _, hm⟩ := he
    exact ⟨m, hm⟩
