-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:10:33.797314+00:00
-- url     : https://prove2.me/submissions/c4a14b7a-28c1-41a4-bc10-8c195b161f60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hHK, hKDrawing, hKMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertex_type__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
      H hcard hdrawing
  exact ⟨K, hHK, hKDrawing,
    WilliamsonShmoys.maximal_planar_drawingOn_has_euler_edge_count__p2m_a4284538_7636_40d4_87e5_69297326a38c_a2
      K hcard hKDrawing hKMax⟩