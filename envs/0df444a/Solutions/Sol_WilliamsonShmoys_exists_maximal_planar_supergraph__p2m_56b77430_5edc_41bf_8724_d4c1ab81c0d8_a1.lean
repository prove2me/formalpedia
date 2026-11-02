-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56b77430_5edc_41bf_8724_d4c1ab81c0d8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:00.99695+00:00
-- url     : https://prove2.me/submissions/c459cae1-e562-440a-b4b7-14ec3d413745

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_exists_maximal_extension__p2m_2521a354_9295_4d68_a93a_2d2a5f622a67_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hMdraw : HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => And (LE.le M N) (And (HasPlanarDrawingOn N)
      (forall K : SimpleGraph V, LE.le N K -> HasPlanarDrawingOn K -> K = N)) := by
  classical
  exact finite_exists_maximal_extension__p2m_2521a354_9295_4d68_a93a_2d2a5f622a67_a1
    (P := HasPlanarDrawingOn) M hMdraw