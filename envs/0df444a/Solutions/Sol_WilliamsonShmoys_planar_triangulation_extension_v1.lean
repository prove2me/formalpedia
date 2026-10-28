-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:00:56.191006+00:00
-- url     : https://prove2.me/submissions/792513c5-c105-4457-a226-d51ee1765b76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_219c2427_f0ca_410a_8cab_2194ee3f8b9c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_219c2427_f0ca_410a_8cab_2194ee3f8b9c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_219c2427_f0ca_410a_8cab_2194ee3f8b9c H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_219c2427_f0ca_410a_8cab_2194ee3f8b9c K hK hCard hMax⟩