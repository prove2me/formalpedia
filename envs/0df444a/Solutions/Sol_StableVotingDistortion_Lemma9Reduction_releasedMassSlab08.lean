-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.releasedMassSlab08
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:44:43.753481+00:00
-- url     : https://prove2.me/submissions/abf49588-4e8d-4dfd-8246-d9d1bdf800e0

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells208To210
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells211To211

open StableVotingDistortion.Lemma9Reduction StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperBox StableVotingDistortion.PaperCurve StableVotingDistortion

theorem combine_cells {α : Type*} (L : List α) (P : α → Prop) (a m k : ℕ)
    (h1 : ∀ cd ∈ (L.drop a).take m, P cd) (h2 : ∀ cd ∈ (L.drop (a + m)).take k, P cd) :
    ∀ cd ∈ (L.drop a).take (m + k), P cd := by
  intro cd hcd
  rw [List.take_add, List.mem_append] at hcd
  rcases hcd with h | h
  · exact h1 cd h
  · rw [List.drop_drop] at h
    exact h2 cd (by simpa [Nat.add_comm] using h)

theorem solution : ∀ cd ∈ (adjacentCells.drop 208).take 4, CellCovered cd.1 cd.2 :=
  (combine_cells adjacentCells (fun cd => CellCovered cd.1 cd.2) 208 3 1 StableVotingDistortion.Lemma9Reduction.coveredCells208To210 (by simpa using StableVotingDistortion.Lemma9Reduction.coveredCells211To211))
