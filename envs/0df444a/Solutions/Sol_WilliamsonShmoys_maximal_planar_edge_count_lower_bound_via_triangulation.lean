-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_via_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:58:55.212669+00:00
-- url     : https://prove2.me/submissions/f5e6c794-c320-4bd8-9f7b-607fdc863dd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_via_maximality

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> Set.Subset L.edgeSet K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨L, hsub, hL, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_via_maximality K hK hV
  have hback : Set.Subset L.edgeSet K.edgeSet := hmax L hsub hL
  have heq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hsub hback
  have hcard : K.edgeSet.ncard = L.edgeSet.ncard := by rw [heq]
  omega