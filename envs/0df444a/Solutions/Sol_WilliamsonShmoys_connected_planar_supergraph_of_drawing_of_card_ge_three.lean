-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph_of_drawing_of_card_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:37:08.084539+00:00
-- url     : https://prove2.me/submissions/1555f80c-1d33-4699-8cbd-d00bd78c1ee6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_on_finite_ordered_type
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawingOn_connected_of_card_ge_three

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by
  obtain ⟨K, hJK, hKplanar, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on_finite_ordered_type J hJ
  exact ⟨K, hJK, hKplanar,
    WilliamsonShmoys.edge_maximal_drawingOn_connected_of_card_ge_three K hKplanar hV hmax⟩