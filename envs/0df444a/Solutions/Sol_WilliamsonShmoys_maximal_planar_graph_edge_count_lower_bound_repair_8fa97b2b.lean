-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_repair_8fa97b2b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:50:13.231696+00:00
-- url     : https://prove2.me/submissions/659e0e10-34cb-441c-a8cf-490b567e7bc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_completion_lower_bound

set_option autoImplicit false

/-- Maximality makes the planar edge completion supplied by the child equal to the original graph. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn N) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hsub, hN, hbound⟩ :=
    WilliamsonShmoys.planar_graph_edge_completion_lower_bound M hV hM
  have hEq : M.edgeSet = N.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra heM
    apply hmax N
    · exact ⟨hsub, fun hNM => heM (hNM he)⟩
    · exact hN
  simpa only [hEq] using hbound