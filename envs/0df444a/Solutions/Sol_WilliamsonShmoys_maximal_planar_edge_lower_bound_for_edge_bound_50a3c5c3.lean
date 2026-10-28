-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:23:18.517083+00:00
-- url     : https://prove2.me/submissions/42a723cd-40d5-42ca-af41-67a32af2df49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V)
    (hQmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  obtain ⟨R, hQR, hRdraw, hCount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_completion_edge_count Q hQdraw hCard
  have hRQ : R ≤ Q := hQmax R hQR hRdraw
  have hEq : Q = R := le_antisymm hQR hRQ
  have hBound : 3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by omega
  simpa [hEq] using hBound