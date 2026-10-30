-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_ctx816e1e7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:55:14.411471+00:00
-- url     : https://prove2.me/submissions/41200a64-a6b1-401a-a488-fa86cc665460

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_ctx816e1e7
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ctx816e1e7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : HasPlanarDrawingOn W) :
    ∃ Q : SimpleGraph V,
      W ≤ Q ∧ HasPlanarDrawingOn Q ∧
        Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨Q, hWQ, hQ, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_ctx816e1e7 W hV hW
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_ctx816e1e7 Q hV hQ hmax
  exact ⟨Q, hWQ, hQ, hcount⟩
