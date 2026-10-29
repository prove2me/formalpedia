-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:37:47.034041+00:00
-- url     : https://prove2.me/submissions/7a6424bd-f3a5-49cb-b38a-a209edb34772

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    (3 : Int) * (Fintype.card V : Int) - 6 <=
      (M.edgeSet.ncard : Int) := by
  obtain ⟨K, hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c
      M hV hM
  have hKM : K = M := hmax K hsub hdraw
  subst K
  omega