-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:23:59.554004+00:00
-- url     : https://prove2.me/submissions/054e692e-499a-4c07-ac24-e9c291d8c564
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound_20261026
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_max_20261026

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_simple_edge_upper_bound_20261026 K hK hV
  by_contra hne
  have hlt : K.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨J, hKJ, hJne, hJplanar⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_below_max_20261026 K hK hV hlt
  exact hJne (hMax J hKJ hJplanar)