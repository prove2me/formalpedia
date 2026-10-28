-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:10:26.935606+00:00
-- url     : https://prove2.me/submissions/b11edd55-5b35-465e-bb31-3695e8755f7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hBound⟩ :=
    WilliamsonShmoys.planar_drawing_has_dense_supergraph G hG hV
  have hKG : K.edgeSet ⊆ G.edgeSet := hmax K hGK hK
  have hEq : G.edgeSet = K.edgeSet := Set.Subset.antisymm hGK hKG
  rw [hEq]
  exact hBound