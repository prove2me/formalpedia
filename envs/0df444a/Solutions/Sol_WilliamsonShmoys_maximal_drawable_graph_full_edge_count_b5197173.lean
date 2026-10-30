-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_full_edge_count_b5197173
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:35:04.382308+00:00
-- url     : https://prove2.me/submissions/b09bda8a-762c-433e-a2b1-2502212d2bd1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b5197173
import Theorems.Thm_WilliamsonShmoys_drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_b5197173 M hV hM
  have hlower : 3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
    by_contra hnot
    have hsmall : M.edgeSet.ncard < 3 * Fintype.card V - 6 :=
      Nat.lt_of_not_ge hnot
    obtain ⟨N, hMN, hNe, hN⟩ :=
      WilliamsonShmoys.drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173
        M hV hM hsmall
    exact hNe (hmax N hMN hN)
  omega