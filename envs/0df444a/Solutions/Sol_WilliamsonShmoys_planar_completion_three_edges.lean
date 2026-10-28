-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_three_edges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:13:48.837394+00:00
-- url     : https://prove2.me/submissions/adb4f2fd-5aed-4be4-99fe-05f7339c20db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_repair_d02dec5c
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_repair_d02dec5c

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNplanar : HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K /\ HasPlanarDrawingOn K /\
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_repair_d02dec5c N hNplanar
  exact ⟨K, hNK, hKplanar,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_d02dec5c
      K hKplanar hV hKmax⟩