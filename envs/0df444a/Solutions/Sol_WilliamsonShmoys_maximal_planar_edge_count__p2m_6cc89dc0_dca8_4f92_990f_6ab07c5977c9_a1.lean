-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:46:00.076349+00:00
-- url     : https://prove2.me/submissions/34e07bb5-8a8f-42e9-92eb-ca748f6e6b39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : HasPlanarDrawingOn T)
    (hmax : forall T' : SimpleGraph V, LE.le T T' -> HasPlanarDrawingOn T' -> T' = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T', hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1 T hV hT
  simpa [hmax T' hsub hdraw] using hcount