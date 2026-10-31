-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:28.83396+00:00
-- url     : https://prove2.me/submissions/de22c80e-ce42-433e-b51f-bebccf468623
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
    M hV hM
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
    M hV hM hMax
  omega