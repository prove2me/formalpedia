-- Prove2me | solution 1 for PrefSemimetric.TopDiff.dmu_isSemimetric
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:55:05.61792+00:00
-- url     : https://prove2.me/submissions/7e73329b-f77c-4cc2-942f-3f178b3e62db

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    IsSemimetric (Dmu w) := by
  intro R T U _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Dmu
    exact Finset.sum_nonneg (fun S _ => Finset.sum_nonneg (fun x _ => hw x))
  · unfold Dmu
    simp
  · unfold Dmu
    apply Finset.sum_congr rfl
    intro S _
    rw [symmDiff_comm]
  · unfold Dmu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S _
    calc ∑ x ∈ symmDiff (maxSet S R) (maxSet S U), w x
        ≤ ∑ x ∈ symmDiff (maxSet S R) (maxSet S T) ∪ symmDiff (maxSet S T) (maxSet S U), w x :=
          Finset.sum_le_sum_of_subset_of_nonneg (symmDiff_triangle _ _ _)
            (fun x _ _ => hw x)
      _ ≤ _ := by
          have h1 := Finset.sum_union_inter (s₁ := symmDiff (maxSet S R) (maxSet S T))
            (s₂ := symmDiff (maxSet S T) (maxSet S U)) (f := w)
          have h2 : 0 ≤ ∑ x ∈ symmDiff (maxSet S R) (maxSet S T) ∩ symmDiff (maxSet S T) (maxSet S U), w x :=
            Finset.sum_nonneg (fun x _ => hw x)
          linarith
