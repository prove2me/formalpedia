-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:28:09.411023+00:00
-- url     : https://prove2.me/submissions/4ddb9851-beaa-4d4b-867f-095438536c65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_edge_count K hV hK
  have hLK : L.edgeSet ⊆ K.edgeSet := hmax L hKL hL
  have hEq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  simpa [hEq] using hCount