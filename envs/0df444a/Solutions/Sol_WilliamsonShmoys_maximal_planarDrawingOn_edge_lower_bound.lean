-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planarDrawingOn_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:27:43.070452+00:00
-- url     : https://prove2.me/submissions/65064814-e87d-4b08-8cfc-ee3368461eee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v))
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by
  obtain ⟨K, hGK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_triangulation_edge_bound G hG hV
  have hKG : K = G := hmax K hGK hK
  simpa [hKG] using hbound