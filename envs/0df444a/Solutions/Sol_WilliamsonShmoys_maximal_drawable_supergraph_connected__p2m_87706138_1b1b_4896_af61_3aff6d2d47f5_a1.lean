-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_connected__p2m_87706138_1b1b_4896_af61_3aff6d2d47f5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:24:42.17876+00:00
-- url     : https://prove2.me/submissions/3d270393-d649-4a6c-afe4-10005cda48df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.Connected := by
  by_contra hconn
  obtain ⟨N, hMN, hNe, hN⟩ :=
    WilliamsonShmoys.disconnected_drawable_strict_extension__p2m_638cd013_f422_4f43_912d_3f97f91e2a69_a1
      M hM hV hconn
  exact hNe (hMax N hMN hN)