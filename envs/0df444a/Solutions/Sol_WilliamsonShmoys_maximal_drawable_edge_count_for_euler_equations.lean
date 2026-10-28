-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_for_euler_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:30:27.091171+00:00
-- url     : https://prove2.me/submissions/f048c0d2-7a27-4755-bb5d-352bba312349
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, LE.le L M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> L = M)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  let M := Classical.choose
    (WilliamsonShmoys.planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1 L hL hCard)
  have hData := Classical.choose_spec
    (WilliamsonShmoys.planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1 L hL hCard)
  have hLM : LE.le L M := hData.1
  have hM : WilliamsonShmoys.HasPlanarDrawingOn M := hData.2.1
  have hCount : M.edgeSet.ncard + 6 = 3 * Fintype.card V := hData.2.2
  have hEq : L = M := hMax M hLM hM
  simpa [hEq] using hCount