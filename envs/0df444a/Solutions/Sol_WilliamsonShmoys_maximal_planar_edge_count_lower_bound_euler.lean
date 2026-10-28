-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:46:48.014024+00:00
-- url     : https://prove2.me/submissions/9259fd3e-f93b-42d9-84d1-c87b02e66617
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_euler_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count G hG hcard
  have hKG : K = G := hmax K hGK hK
  subst K
  omega