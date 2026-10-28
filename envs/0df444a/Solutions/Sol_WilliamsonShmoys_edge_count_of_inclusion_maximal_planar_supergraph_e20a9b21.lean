-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_supergraph_e20a9b21
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:54:04.686116+00:00
-- url     : https://prove2.me/submissions/0e04a5f1-ca22-497f-ad0a-244a19d10c0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → L.edgeSet = M.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hM, hSub, hCount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_edge_count L hDrawing hCard
  have hEq := hMax M hM hSub
  rw [hEq]
  exact hCount