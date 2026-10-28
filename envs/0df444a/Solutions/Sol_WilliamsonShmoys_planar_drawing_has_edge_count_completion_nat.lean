-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_count_completion_nat
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:25:19.989714+00:00
-- url     : https://prove2.me/submissions/416fbfb7-569f-47b6-b409-b6ac470492fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_c10b408b_b7ec_40f0_b964_0a6697295590
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_c10b408b_b7ec_40f0_b964_0a6697295590 N hN
  refine ⟨K, hNK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590 K hK hCard hMax