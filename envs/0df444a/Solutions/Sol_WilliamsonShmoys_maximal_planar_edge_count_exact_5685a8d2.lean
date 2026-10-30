-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_exact_5685a8d2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:08:24.650215+00:00
-- url     : https://prove2.me/submissions/07b44647-c71a-4b04-9d4f-3ae93b388855

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      K.edgeSet = G.edgeSet) :
    3 * Fintype.card V = G.edgeSet.ncard + 6 := by
  obtain ⟨K, hSub, hDrawK, hCount⟩ :=
    WilliamsonShmoys.planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3 G hDraw hCard
  have hEq : K.edgeSet = G.edgeSet := hMaximal K hSub hDrawK
  simpa [hEq] using hCount