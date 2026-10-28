-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_tight_planar_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:26:54.136823+00:00
-- url     : https://prove2.me/submissions/f7cf5345-eb82-467b-9e6f-ec5335c50845
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_tight_completion
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_tight_edge_count_for_tight_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      N <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_for_tight_completion N hN
  have hCount :=
    WilliamsonShmoys.maximal_drawable_graph_has_tight_edge_count_for_tight_completion
      K hK hMax hCard
  exact ⟨K, hNK, hK, hCount⟩
