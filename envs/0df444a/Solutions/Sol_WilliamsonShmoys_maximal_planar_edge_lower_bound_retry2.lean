-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_retry2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:08:20.449909+00:00
-- url     : https://prove2.me/submissions/907e8934-e608-466d-8de8-320de49fa970

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by
  obtain ⟨f, hFaces, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_retry2 M hV hM hMax
  omega