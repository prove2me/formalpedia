-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_3649950b_31dd_4927_b1e8_a61f090b394f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:26.351202+00:00
-- url     : https://prove2.me/submissions/1dfecfac-3513-4b28-ac62-e5a230d979a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel U.Adj := Classical.decRel U.Adj
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1 T hT
  refine ⟨U, hTU, hU, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1 U hU hcard hmax