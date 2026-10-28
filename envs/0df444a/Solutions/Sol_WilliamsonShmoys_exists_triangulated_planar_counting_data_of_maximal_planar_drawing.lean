-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_counting_data_of_maximal_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:19:40.542135+00:00
-- url     : https://prove2.me/submissions/f27f0a05-0ec3-4c4b-b8c8-0f0c574aabe5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_counting
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_for_counting
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      L <= K) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarCountingData K) := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_for_counting K hV hK
  have hlower :=
    WilliamsonShmoys.maximal_drawing_edge_lower_bound_for_counting K hV hK hmax
  have hedge :
      (K.edgeSet.ncard : Int) =
        3 * (Fintype.card V : Int) - 6 := by
    omega
  refine ⟨⟨2 * Fintype.card V - 4, ?_, ?_⟩⟩ <;> omega