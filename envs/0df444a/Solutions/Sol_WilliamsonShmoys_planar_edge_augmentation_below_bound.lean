-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:41:48.101626+00:00
-- url     : https://prove2.me/submissions/1c76fef9-ddb4-483e-bc0b-5087601758cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound_a11205c3_51bf_4409_a8f2_455e7e17d8d2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, K.Adj u v ∧ ¬ G.Adj u v := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2 G hG
  have hbound : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_supergraph_edge_bound_a11205c3_51bf_4409_a8f2_455e7e17d8d2 K hK hV hmax
  by_contra hnot
  have hKG : ∀ ⦃u v : V⦄, K.Adj u v → G.Adj u v := by
    intro u v huv
    by_contra hnotG
    exact hnot ⟨K, hGK, hK, ⟨u, v, huv, hnotG⟩⟩
  have hEq : K = G := by
    ext u v
    constructor
    · intro huv
      exact hKG huv
    · intro huv
      exact hGK huv
  exact (not_le_of_gt hE) (by simpa [hEq] using hbound)