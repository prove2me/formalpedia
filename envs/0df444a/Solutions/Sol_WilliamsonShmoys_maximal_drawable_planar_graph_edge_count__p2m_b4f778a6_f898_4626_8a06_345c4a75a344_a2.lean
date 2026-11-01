-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_graph_edge_count__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:02.421291+00:00
-- url     : https://prove2.me/submissions/5ed472a2-42c0-42e3-be62-27fcdf9ee2b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.triangulation_extension__p2m_67af1d40_5710_49f6_8447_77c85edb00fd_a1
      L hcard hL
  have hEq : M = L := hmax M hLM hM
  cases hEq
  exact hcount