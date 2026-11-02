-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:46.274551+00:00
-- url     : https://prove2.me/submissions/b3533153-f27d-42fc-8849-648ac4ac6234
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V, N <= P -> WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    N.Connected := by
  obtain ⟨P, hNP, hPconn, hPplanar⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2 N hN hcard
  have hEq : P = N := hmax P hNP hPplanar
  rw [hEq] at hPconn
  exact hPconn