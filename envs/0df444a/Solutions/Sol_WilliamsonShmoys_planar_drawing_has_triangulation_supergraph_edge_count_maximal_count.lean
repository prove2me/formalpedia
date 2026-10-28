-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:06:25.608507+00:00
-- url     : https://prove2.me/submissions/3b893791-9672-46e7-ae64-8f04a0540a46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count_certificate

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_euler_count_certificate M hV hM hmax
  omega
