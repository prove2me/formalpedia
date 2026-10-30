-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:23:17.616039+00:00
-- url     : https://prove2.me/submissions/bba5a33e-e7c9-45e1-8233-b8693977535d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hEdges : K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_count K hK hmax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega