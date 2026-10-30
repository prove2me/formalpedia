-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_connected__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:50.778888+00:00
-- url     : https://prove2.me/submissions/aeb2c9da-f688-43b1-8163-0f8617899c95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      HasPlanarDrawingOn N -> N = M)
    (hV : 3 <= Fintype.card V) :
    M.Connected := by
  by_contra hNotConnected
  have hAug := WilliamsonShmoys.disconnected_planar_augmentation__p2m_d040595c_f679_4c6d_8e62_deaf65883107_a1
    M hM hNotConnected hV
  cases hAug with
  | intro N hRest =>
    cases hRest with
    | intro hMN hRest =>
      cases hRest with
      | intro hNM hNPlanar =>
        exact hNM (hMax N hMN hNPlanar)