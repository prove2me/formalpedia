-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_50a3c5c3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:08:53.815223+00:00
-- url     : https://prove2.me/submissions/ac7b410f-7ffc-4554-84bc-a4fd416bf867
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_edge_bound_50a3c5c3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V)
    (hQmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q) :
    Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound_for_edge_bound_50a3c5c3 Q hQdraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3 Q hQdraw hCard hQmax
  omega