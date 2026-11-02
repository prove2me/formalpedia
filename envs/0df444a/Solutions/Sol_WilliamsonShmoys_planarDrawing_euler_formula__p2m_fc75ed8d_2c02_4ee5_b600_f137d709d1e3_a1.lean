-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:35:22.397438+00:00
-- url     : https://prove2.me/submissions/d2789f25-5010-428c-b8cf-0103f45bb33c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected) :
    Exists fun f : Nat =>
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by
  exact WilliamsonShmoys.planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
    G dG hConn hG