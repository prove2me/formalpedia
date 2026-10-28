-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_lower_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:17:02.638414+00:00
-- url     : https://prove2.me/submissions/2ce896ce-9d2e-4425-833b-0c92d4528f19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_repair3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_extension_repair3 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_bound_repair3 L hL hCard hMax⟩