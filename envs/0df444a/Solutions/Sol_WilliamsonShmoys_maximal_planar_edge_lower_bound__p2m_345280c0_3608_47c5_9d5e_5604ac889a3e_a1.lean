-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:05:26.194972+00:00
-- url     : https://prove2.me/submissions/bb782fbd-61cf-4e03-b8bc-7c1790cd4428
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by
  classical
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
      H hV hH
  have hEq : K = H := hmax K hHK hK
  subst K
  exact Nat.le_of_eq hcount