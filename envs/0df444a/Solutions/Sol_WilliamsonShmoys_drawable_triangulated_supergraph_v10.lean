-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulated_supergraph_v10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:31:57.582638+00:00
-- url     : https://prove2.me/submissions/9dd6fa74-6f83-46ee-a733-e7e62a41029e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_v10_aux
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_v10_aux

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_v10_aux L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_drawable_edge_count_v10_aux M hV hM hmax⟩