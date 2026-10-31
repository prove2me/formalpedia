-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:04.897522+00:00
-- url     : https://prove2.me/submissions/83a8b9de-41bc-4c9f-8481-f054ae3d5f27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet := by
  exact WilliamsonShmoys.finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
    HasPlanarDrawingOn
    (by
      intro G H hHG hG
      exact WilliamsonShmoys.planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1 G H hHG hG)
    N hN