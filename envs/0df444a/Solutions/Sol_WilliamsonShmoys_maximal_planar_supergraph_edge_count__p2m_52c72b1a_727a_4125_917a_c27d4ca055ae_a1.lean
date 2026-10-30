-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:35:26.374988+00:00
-- url     : https://prove2.me/submissions/05d276a0-9ae6-4d26-b689-a1d8c4660e23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn N)
    (hMaximal : ∀ K : SimpleGraph V,
      N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hKDraw, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1
      N hCard hDraw
  have hKN : K = N := hMaximal K hNK hKDraw
  simpa [hKN] using hCount