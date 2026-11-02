-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:55.354704+00:00
-- url     : https://prove2.me/submissions/f98b154b-2fc5-4c6c-b9ef-cfd37af50a5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.Connected := by
  by_contra hconn
  obtain ⟨P, hNP, hPN, hP⟩ :=
    WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_eec88a46_e2f1_426a_bbcb_0322b031599d_a1
      N hcard hN hconn
  exact hPN (hmax P hNP hP)