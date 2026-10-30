-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_36583a35
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:19:40.070594+00:00
-- url     : https://prove2.me/submissions/570efdc7-1bf1-4648-a1b9-fbeec8abdfd0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion_36583a35_retry3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M <= L) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hLK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_completion_36583a35_retry3 L hL hCard
  have hKL : K <= L := hMax K hLK hK
  have hEq : L = K := le_antisymm hLK hKL
  rw [hEq]
  exact hCount