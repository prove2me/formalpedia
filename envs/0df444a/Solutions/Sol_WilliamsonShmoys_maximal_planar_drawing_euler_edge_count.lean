-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:43:38.27902+00:00
-- url     : https://prove2.me/submissions/4a8e6651-6125-4719-b1f9-92e8f811fa5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_euler_edge_count N hV hN
  have hKN : K = N := hMax K hNK hKplanar
  rw [← hKN]
  exact hKcount