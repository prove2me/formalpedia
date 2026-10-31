-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:56:57.531615+00:00
-- url     : https://prove2.me/submissions/beecbf1c-bbea-49c9-8c36-df076be1806e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
import Theorems.Thm_SimpleGraph_exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  exact SimpleGraph.exists_maximal_supgraph_of_finite__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (fun {G H} hHG hG =>
      WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_2dea5b09_c429_4a5e_b3c1_b82fac24916e_a2 hHG hG)
    K hK
