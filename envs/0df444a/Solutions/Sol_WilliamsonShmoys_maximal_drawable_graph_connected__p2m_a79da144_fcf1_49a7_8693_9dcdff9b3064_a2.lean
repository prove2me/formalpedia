-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:08.513015+00:00
-- url     : https://prove2.me/submissions/a9e214ad-5c2c-472a-b5c9-9f79ddf1d22a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1

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
    WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1
      M hM hconn
  exact hnotNM (hmax N hMN hN)