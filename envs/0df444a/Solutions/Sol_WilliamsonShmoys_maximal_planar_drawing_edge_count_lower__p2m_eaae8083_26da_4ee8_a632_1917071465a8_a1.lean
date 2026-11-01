-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:19:28.585908+00:00
-- url     : https://prove2.me/submissions/116bfc6e-2ca0-47e1-9959-81fa7852e9c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V <= L.edgeFinset.card + 6 := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_1cb61011_99ad_4f9a_a1ee_f080a0059de3_a2
      L hcard hL
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hML : M = L := hmax M hLM hM
  subst M
  exact le_of_eq hcount.symm