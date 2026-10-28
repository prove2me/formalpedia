-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_with_triangulated_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:28:06.510867+00:00
-- url     : https://prove2.me/submissions/b20d8500-9ab2-428d-83ab-c1d15c0e34fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_completion_maximal_drawable_supergraph_36583a35
import Theorems.Thm_WilliamsonShmoys_completion_maximal_drawable_edge_count_36583a35

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.completion_maximal_drawable_supergraph_36583a35 N hN
  have hCount :=
    WilliamsonShmoys.completion_maximal_drawable_edge_count_36583a35 K hK hMax hCard
  exact ⟨K, hNK, hK, hCount⟩