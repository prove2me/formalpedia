-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:20.621851+00:00
-- url     : https://prove2.me/submissions/c44e7f6e-80bf-4717-9c9a-e5489d8b748a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
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
    WilliamsonShmoys.disconnected_drawable_extension__p2m_34e3c7ce_8936_45db_894d_7bc025c10cb3_a2
      K hK hcard hnot
  have hLK : L = K := hmax L hKL hL
  exact hneq hLK
