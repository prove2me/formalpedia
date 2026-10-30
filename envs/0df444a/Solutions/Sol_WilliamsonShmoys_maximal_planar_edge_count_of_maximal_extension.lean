-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_of_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:57:14.027839+00:00
-- url     : https://prove2.me/submissions/e3a8c452-aa6f-4e63-b681-587d40b9fd39

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_counting_data_of_maximal_planar_drawing
import Theorems.Thm_WilliamsonShmoys_edge_count_of_triangulated_planar_counting_data
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
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨D⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_counting_data_of_maximal_planar_drawing
      K hV hK hmax
  exact WilliamsonShmoys.edge_count_of_triangulated_planar_counting_data K D