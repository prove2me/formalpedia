-- Prove2me | solution 1 for WilliamsonShmoys.connected_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:27.374763+00:00
-- url     : https://prove2.me/submissions/f42e6e3c-e4c5-4720-a468-3e90d285605e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    H.Connected := by
  by_contra hconn
  obtain ⟨u, v, huv, hnotReachable⟩ :=
    WilliamsonShmoys.disconnected_nonreachable_vertices__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
      H hV hconn
  obtain ⟨J, hHJ, hJ, hnotBack⟩ :=
    WilliamsonShmoys.planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
      H hH huv hnotReachable
  exact hnotBack (hmax J hHJ hJ)