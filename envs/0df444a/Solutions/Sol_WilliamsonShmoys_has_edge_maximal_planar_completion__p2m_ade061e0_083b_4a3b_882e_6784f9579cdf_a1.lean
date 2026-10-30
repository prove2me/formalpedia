-- Prove2me | solution 1 for WilliamsonShmoys.has_edge_maximal_planar_completion__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:32:00.589373+00:00
-- url     : https://prove2.me/submissions/57f08b43-c672-4fc5-8951-1ab3fefd1a8d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_element_for_graph_predicate__p2m_a6c79c1c_4522_4952_80c8_2c98cd425351_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  obtain ⟨K, hK, hMK, hmax⟩ :=
    exists_maximal_element_for_graph_predicate__p2m_a6c79c1c_4522_4952_80c8_2c98cd425351_a2
      P M hM
  refine ⟨K, hMK, hK, ?_⟩
  intro L hproper hL
  exact hproper.2 (hmax L hL hproper.1)