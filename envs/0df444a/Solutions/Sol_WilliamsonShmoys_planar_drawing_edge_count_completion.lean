-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:05:05.017405+00:00
-- url     : https://prove2.me/submissions/137f6dbf-4eba-4b9a-8c7c-c15b8619f5a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_4c3a3861
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_4c3a3861

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hNK, hK, hcount, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_4c3a3861 N hN hCard
  have hEq :=
    WilliamsonShmoys.maximal_planar_edge_count_4c3a3861 K hK hCard hmax
  exact ⟨K, hNK, hK, hcount, hEq⟩