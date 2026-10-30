-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:03:56.843959+00:00
-- url     : https://prove2.me/submissions/40e3fad7-0274-4c74-afd2-54b11566f4c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound_count_79011c86fe2a4d17

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V => And (M <= N)
      (And (WilliamsonShmoys.HasPlanarDrawingOn N)
        (3 * Fintype.card V <= N.edgeSet.ncard + 6)) := by
  have hExt :=
    WilliamsonShmoys.planar_maximal_extension_edge_bound_extension_79011c86fe2a4d17 M hM
  cases hExt with
  | intro N hN =>
    have hMN : M <= N := hN.1
    have hPlanar : WilliamsonShmoys.HasPlanarDrawingOn N := hN.2.1
    have hmax := hN.2.2
    have hcount :=
      WilliamsonShmoys.planar_maximal_extension_edge_bound_count_79011c86fe2a4d17
        N hV hPlanar hmax
    refine Exists.intro N (And.intro hMN (And.intro hPlanar ?_))
    rw [hcount]
    omega