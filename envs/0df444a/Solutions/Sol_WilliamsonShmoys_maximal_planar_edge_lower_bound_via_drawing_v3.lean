-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_via_drawing_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:27:49.961489+00:00
-- url     : https://prove2.me/submissions/1bac82fc-bf5b-467a-8109-d7c6b67c719b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_extension N hV hN
  have hEq : K = N := hmax K hNK hK
  rw [hEq] at hbound
  exact hbound