-- Prove2me | solution 1 for StabilityConjecture.cr_stability_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T20:22:25.010968+00:00
-- url     : https://prove2.me/submissions/b82219e2-8a17-4ced-8cb2-670ed6d30889
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic
import Theorems.Thm_StabilityConjecture_mane_C1_stability
import Theorems.Thm_StabilityConjecture_cr_stability_conjecture_two_le

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open StabilityConjecture ClosingLemma

theorem solution {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : Diff n M r) (hf : IsStructurallyStable r f) :
    SatisfiesAxiomA f := by
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · obtain rfl : r = 1 := by omega
    exact mane_C1_stability f hf
  · exact cr_stability_conjecture_two_le r h2 f hf
