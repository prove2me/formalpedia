-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:41:29.134324+00:00
-- url     : https://prove2.me/submissions/f0537d22-7300-450f-9402-26057b7faeeb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * (Fintype.card V : Int) - 6 ≤ (N.edgeSet.ncard : Int) := by
  obtain ⟨K, hNK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion N hN hCard
  have hEq : K = N := hMax K hK hNK
  subst K
  rw [hCount]