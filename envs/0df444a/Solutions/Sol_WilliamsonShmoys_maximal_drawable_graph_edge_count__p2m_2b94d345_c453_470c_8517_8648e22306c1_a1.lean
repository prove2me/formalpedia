-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:28:55.972527+00:00
-- url     : https://prove2.me/submissions/fef6bf7d-f9bf-444d-bb1f-aa186a6fd2f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, L ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_8d118255_640d_459b_9d55_e13b141f8172_a1
      L hL hV
  have hKL : K ≤ L := hMax K hLK hK
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hcard