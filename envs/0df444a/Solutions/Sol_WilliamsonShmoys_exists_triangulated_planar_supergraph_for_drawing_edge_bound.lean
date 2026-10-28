-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_for_drawing_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:06:11.976838+00:00
-- url     : https://prove2.me/submissions/7085666b-0fc3-489c-ac32-c8a404f843f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_drawing_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_drawing_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    Exists fun H : SimpleGraph V => M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_drawing_edge_bound M hMdraw
  have hmaxH : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet := by
    intro K hHK hKdraw
    exact hmax K (hsub.trans hHK) hKdraw
  exact ⟨H, hsub, hdraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_drawing_edge_bound
      H hV hdraw hmaxH⟩