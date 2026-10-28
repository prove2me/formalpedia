-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:24:08.371734+00:00
-- url     : https://prove2.me/submissions/6d5933fb-e83c-43e7-9d09-862e868c393f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph

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
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_supergraph K hV hK
  have hLK : L.edgeSet ⊆ K.edgeSet := hmax L hKL hLplanar
  have hsets : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  simpa [hsets] using hLcount