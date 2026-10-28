-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_strict_supergraph_of_not_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:39:40.393918+00:00
-- url     : https://prove2.me/submissions/e42fe1dd-fc5f-497c-9958-f8a05814a3e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected
import Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_unreachable_pair

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hdis : Not G.Connected) :
    Exists fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H) (Not (H <= G))) := by
  have hpair :=
    WilliamsonShmoys.exists_unreachable_pair_of_not_connected G hV hdis
  cases hpair with
  | intro u hrest =>
    cases hrest with
    | intro v huv =>
      exact WilliamsonShmoys.exists_drawable_strict_supergraph_of_unreachable_pair
        G hdraw u v huv