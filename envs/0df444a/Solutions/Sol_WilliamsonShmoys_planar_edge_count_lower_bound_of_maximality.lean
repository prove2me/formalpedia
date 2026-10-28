-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_lower_bound_of_maximality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:23:56.287995+00:00
-- url     : https://prove2.me/submissions/0d6a2c49-73eb-4939-8c54-b3ca3da6cd66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_dense_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hMax : forall K : SimpleGraph V, H <= K ->
      HasPlanarDrawingOn K -> K <= H)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hBound⟩ :=
    WilliamsonShmoys.planar_drawable_dense_extension H hH hCard
  have hKH : K <= H := hMax K hHK hK
  have hEdges : K.edgeSet = H.edgeSet := by
    apply Set.Subset.antisymm
    · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hKH
    · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hHK
  simpa [hEdges] using hBound