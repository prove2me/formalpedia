-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_drawable_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:07:51.956918+00:00
-- url     : https://prove2.me/submissions/acb2113f-1e91-4d84-9a34-159ce5d8410d

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  have hcount := WilliamsonShmoys.planar_completion_edge_count M hV hMdraw hMmax
  calc
    3 * Fintype.card V - 6 = M.edgeSet.ncard := hcount.symm
    _ ≤ M.edgeSet.ncard := le_rfl