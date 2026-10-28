-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_card
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:56:43.304859+00:00
-- url     : https://prove2.me/submissions/a7814bf2-e797-4d73-b327-01ecdc5bbc8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_b74a49f4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_b74a49f4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_b74a49f4 J hJ
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.maximal_planar_edge_card_b74a49f4 K hK hCard hmax⟩