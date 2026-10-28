-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_b5197173
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:53:41.687201+00:00
-- url     : https://prove2.me/submissions/2a7f1cc8-4860-47d2-95b1-eb2320e60472
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_dense_supergraph

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ P : SimpleGraph V, M ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨P, hMP, hP, hbound⟩ :=
    WilliamsonShmoys.drawable_graph_has_dense_supergraph M hV hM
  have hEq : P = M := hmax P hMP hP
  rw [← hEq]
  exact hbound