-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_1b538d07
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:07:48.524835+00:00
-- url     : https://prove2.me/submissions/3b586993-f31a-4ab1-b8fc-5dcb39fe8b43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> (K ≠ L) ->
      (¬ WilliamsonShmoys.HasPlanarDrawingOn L)) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulated_completion K hV hK
  have hEq : K = L := by
    by_contra hne
    exact (hmax L hKL hne) hL
  simpa [hEq] using (Nat.le_of_eq hcount)