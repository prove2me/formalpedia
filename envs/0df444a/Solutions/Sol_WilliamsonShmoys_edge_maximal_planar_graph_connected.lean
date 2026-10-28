-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:59:28.900665+00:00
-- url     : https://prove2.me/submissions/c41326ba-9fec-40a4-a9fb-f5a8b898c944
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_of_disconnected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    ∀ u v, Relation.ReflTransGen H.Adj u v := by
  classical
  intro u v
  by_contra hconn
  obtain ⟨K, hsub, hplanar, hmore⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_of_disconnected
      H hH hV (by
        intro hconnected
        exact hconn (hconnected u v))
  have hbound : K.edgeSet.ncard ≤ H.edgeSet.ncard := hmax K hsub hplanar
  omega