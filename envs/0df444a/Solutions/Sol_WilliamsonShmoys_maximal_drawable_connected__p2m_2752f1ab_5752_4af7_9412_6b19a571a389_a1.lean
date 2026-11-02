-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:16:55.546844+00:00
-- url     : https://prove2.me/submissions/7240885d-1f25-4fb9-b4f1-332be1323353

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected_from_maximality_afa305d5

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.Connected := by
  classical
  exact WilliamsonShmoys.maximal_planar_drawing_connected_from_maximality_afa305d5
    M hM hcard (by
      intro N hMN hN
      exact hmax N inferInstance hMN hN)
