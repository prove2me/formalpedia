-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:28.017201+00:00
-- url     : https://prove2.me/submissions/a167242b-0140-4e68-bb87-a75aa43479f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.Connected := by
  by_contra hnot
  obtain ⟨L, hKL, hneq, hL⟩ :=
    WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a1
      K hK hnot
  have hLK : L = K := hmax L hKL hL
  exact hneq hLK