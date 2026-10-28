-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:59:10.162428+00:00
-- url     : https://prove2.me/submissions/25216e3c-82c7-44d4-8e25-0ad5035bf475
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, J ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = J) :
    3 * Fintype.card V - 6 ≤ J.edgeSet.ncard := by
  obtain ⟨L, hJL, hL, hEdges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_20261026 J hJ hV
  have hEq : L = J := hMax L hJL hL
  rw [← hEq]
  exact le_of_eq hEdges