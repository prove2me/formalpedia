-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_a8911ec3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:53:37.808759+00:00
-- url     : https://prove2.me/submissions/7fcbeb12-c848-4176-bc1a-df5a670d230d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_c00979a8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists_c00979a8 N hV hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8 K hV hK hmax⟩