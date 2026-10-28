-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:01:18.699403+00:00
-- url     : https://prove2.me/submissions/d5cdfeef-3cf8-4300-81d4-5b1e0a81556b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_v2_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_v2_maximal_extension_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    Q.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hQK, hK, hmax, hcount⟩ :=
    WilliamsonShmoys.planar_edge_bound_v2_exists_maximal_extension Q hQ
  have hKcount :=
    WilliamsonShmoys.planar_edge_bound_v2_maximal_extension_count K hV hK hmax
  exact hcount.trans_eq hKcount
