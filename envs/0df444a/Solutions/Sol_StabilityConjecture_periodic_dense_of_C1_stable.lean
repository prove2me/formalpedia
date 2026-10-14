-- Prove2me | solution 1 for StabilityConjecture.periodic_dense_of_C1_stable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T20:15:42.572498+00:00
-- url     : https://prove2.me/submissions/745dbd04-0c60-495a-b9a8-79bdfed800f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic
import Theorems.Thm_StabilityConjecture_mane_C1_stability

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open StabilityConjecture ClosingLemma

theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : Diff n M 1) (hf : IsStructurallyStable 1 f) :
    closure (Function.periodicPts f) = PughClosingLemma.nonwanderingSet f :=
  (mane_C1_stability f hf).2
