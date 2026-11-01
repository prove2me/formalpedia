-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:05.399201+00:00
-- url     : https://prove2.me/submissions/c56d2d24-5192-4883-862f-f68945d93a01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_bf0a7b72_11ad_4656_97eb_ed64d269b026_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      ∀ u v, L.Adj u v → K.Adj u v) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨N, hKN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bf0a7b72_11ad_4656_97eb_ed64d269b026_a1
      K hCard hK
  have hNK : ∀ u v, N.Adj u v → K.Adj u v := hmax N hKN hN
  have hAdj : N.Adj = K.Adj := by
    funext u v
    apply propext
    exact ⟨hNK u v, hKN u v⟩
  have hEq : N = K := SimpleGraph.ext hAdj
  rw [hEq] at hCount
  exact hCount