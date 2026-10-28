-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximal_planar_count_92703542_9701_452c_b6a8_363f18bf7214
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:12:40.601414+00:00
-- url     : https://prove2.me/submissions/d8286fdb-83d2-4b51-96c2-6f2da9ccbab9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_completion_repair_025e7f85
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_repair_025e7f85

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_completion_repair_025e7f85 H hH
  have hCount :=
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_025e7f85 K hK hCard hMax
  exact ⟨K, hHK, hK, hCount⟩
