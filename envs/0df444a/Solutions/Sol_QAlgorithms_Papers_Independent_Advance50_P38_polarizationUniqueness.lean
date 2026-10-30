-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.polarizationUniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:21:22.114672+00:00
-- url     : https://prove2.me/submissions/a341b726-e1d5-4d57-9344-6ea7de0fb3c1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (beta : H → ℝ)
    (hbeta : IsBoundedQuadratic beta) :
    (∃! B : H →L[ℝ] H →L[ℝ] ℝ,
      (∀ v w, B v w = B w v) ∧ ∀ v, beta v = B v v) ∧
    ∀ B : H →L[ℝ] H →L[ℝ] ℝ, (∀ v w, B v w = B w v) →
      (∀ v, beta v = B v v) →
      ∀ v w, B v w = (beta (v + w) - beta v - beta w) / 2 := by
  have pol : ∀ B : H →L[ℝ] H →L[ℝ] ℝ, (∀ v w, B v w = B w v) →
      (∀ v, beta v = B v v) → ∀ v w, B v w = (beta (v + w) - beta v - beta w) / 2 := by
    intro B hs hb v w
    rw [hb (v + w), hb v, hb w]
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [hs w v]; ring
  refine ⟨?_, pol⟩
  obtain ⟨B, hs, hb⟩ := hbeta
  refine ⟨B, ⟨hs, hb⟩, ?_⟩
  rintro B' ⟨hs', hb'⟩
  ext v w
  rw [pol B' hs' hb' v w, pol B hs hb v w]
