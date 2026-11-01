-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:03.234113+00:00
-- url     : https://prove2.me/submissions/2531bf55-320f-4dc4-9acd-e29b1f48f1b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.Connected := by
  by_contra hconn
  obtain ⟨N, hMN, hN, hnotNM⟩ :=
    WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a2
      M hcard hM hconn
  exact hnotNM (hmax N hMN hN)