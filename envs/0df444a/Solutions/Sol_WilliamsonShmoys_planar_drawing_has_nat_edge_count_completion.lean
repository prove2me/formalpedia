-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:45:07.890457+00:00
-- url     : https://prove2.me/submissions/dd98215b-ae41-4f5a-b558-2ced22ffb978

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion_finite_maximal_extension_553ae5ef
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion_maximal_edge_count_553ae5ef

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_finite_maximal_extension_553ae5ef
      N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion_maximal_edge_count_553ae5ef
      K hK hmax hCard⟩