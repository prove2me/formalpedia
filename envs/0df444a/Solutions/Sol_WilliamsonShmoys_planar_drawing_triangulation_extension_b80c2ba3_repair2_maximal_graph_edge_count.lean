-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:38:12.911287+00:00
-- url     : https://prove2.me/submissions/a051bf57-17dd-492e-bf1c-9ef482b037ca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet →
      P.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hP, hNP, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_extension_to_triangulation N hCard hN
  have hPN : P.edgeSet ⊆ N.edgeSet := hmax P hP hNP
  have hEq : N.edgeSet = P.edgeSet := Set.Subset.antisymm hNP hPN
  have hcard : N.edgeSet.ncard = P.edgeSet.ncard := congrArg Set.ncard hEq
  rw [hcard]
  exact hcount