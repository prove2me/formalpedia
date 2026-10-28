-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count_20261028
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:35:10.511003+00:00
-- url     : https://prove2.me/submissions/92bf2f0e-12b0-4498-9a79-7d83cdb562e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_triangulated_euler_data
import Theorems.Thm_WilliamsonShmoys_triangulation_euler_data_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨data⟩ :=
    WilliamsonShmoys.maximal_drawable_has_triangulated_euler_data K hK hCard hmax
  exact WilliamsonShmoys.triangulation_euler_data_edge_count K data
