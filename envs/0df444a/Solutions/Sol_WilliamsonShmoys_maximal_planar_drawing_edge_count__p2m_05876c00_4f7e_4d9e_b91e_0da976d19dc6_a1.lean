-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:10.646321+00:00
-- url     : https://prove2.me/submissions/1fe58216-f984-42e0-b439-a904768a8f36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      ∀ u v, N.Adj u v → M.Adj u v) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1
      M hM hCard
  have hNM : ∀ u v, N.Adj u v → M.Adj u v := hMax N hMN hN
  have hGraph : N = M := by
    ext u v
    exact ⟨hNM u v, hMN u v⟩
  simpa [hGraph] using hCount