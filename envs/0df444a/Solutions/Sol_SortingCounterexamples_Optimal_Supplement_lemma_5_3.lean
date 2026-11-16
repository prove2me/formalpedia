-- Prove2me | solution 1 for SortingCounterexamples.Optimal.Supplement.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:30:16.558604+00:00
-- url     : https://prove2.me/submissions/96bf4a8a-6d6b-4ba7-97fe-6995033b33ce

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

open SortingCounterexamples.Optimal SortingCounterexamples.Optimal.Supplement

theorem solution {n d : ℕ} (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n))
    (hH : IsGeometricClass v H) (hne : H.Nonempty) (h : Transcript n) (πhat : Ranking n)
    (hext : IsLinearExtension πhat (MajorityEdge d H h)) :
    ∀ i j : Fin n, πhat.Before i j → 1 / ((d : ℝ) + 1) ≤ pairProb H h i j := by
  classical
  intro i j hij
  have hne_ij : i ≠ j := by
    rintro rfl; exact lt_irrefl _ hij
  have hwpos : ∀ π, 0 < weight h π := fun π => by unfold weight; positivity
  have hQ : 0 < totalWeight H h := Finset.sum_pos (fun π _ => hwpos π) hne
  -- p(i,j) + p(j,i) = 1
  have hsum : pairProb H h i j + pairProb H h j i = 1 := by
    unfold pairProb
    rw [← add_div, div_eq_one_iff_eq hQ.ne']
    have hsplit := Finset.sum_filter_add_sum_filter_not H (fun π : Ranking n => π.Before i j)
      (fun π => weight h π)
    have hcongr : H.filter (fun π : Ranking n => ¬ π.Before i j) =
        H.filter (fun π : Ranking n => π.Before j i) := by
      apply Finset.filter_congr
      intro π _
      unfold Ranking.Before
      have hne' : π.symm i ≠ π.symm j := fun e => hne_ij (π.symm.injective e)
      constructor
      · intro hn; exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hne')
      · intro hl; exact not_lt.mpr hl.le
    rw [hcongr] at hsplit
    unfold totalWeight
    exact hsplit
  by_contra hlt
  push Not at hlt
  have hji : MajorityEdge d H h j i := by
    refine ⟨Ne.symm hne_ij, ?_⟩
    linarith
  have := hext j i hji
  unfold Ranking.Before at this hij
  exact lt_asymm hij this
