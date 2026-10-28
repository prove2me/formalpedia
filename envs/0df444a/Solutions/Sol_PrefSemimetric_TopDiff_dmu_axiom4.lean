-- Prove2me | solution 1 for PrefSemimetric.TopDiff.dmu_axiom4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:57:32.272649+00:00
-- url     : https://prove2.me/submissions/a29c7e59-2f74-4f59-a5cc-683720abb57d

import Mathlib
import Definitions.Def_PrefSemimetric_TopDiff_Model

open PrefSemimetric.TopDiff

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    Axiom4 (Dmu w) := by
  intro R T _ _ h
  have hmax : ∀ S : Finset X, maxSet S R = maxSet S T := by
    intro S
    ext x
    simp only [maxSet, Finset.mem_filter, h]
  unfold Dmu
  simp [hmax]
