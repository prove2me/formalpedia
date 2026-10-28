-- Prove2me | solution 2 for SionMinimax.KKM.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:12:20.491442+00:00
-- url     : https://prove2.me/submissions/05f6c3ea-920b-409d-8255-df56d129e084

import Mathlib
import Theorems.Thm_KKM_iInter_nonempty

-- `SionMinimax.KKM.theorem_3_1` is `KKM.iInter_nonempty` with one hypothesis more than it
-- needs: the affine independence of the points is never used.

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E) (haff : AffineIndependent ℝ a)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    (⋂ i, A i).Nonempty :=
  KKM.iInter_nonempty n a A hA hcov hconv hv
