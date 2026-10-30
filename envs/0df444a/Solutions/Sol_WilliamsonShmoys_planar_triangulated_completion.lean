-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:04:10.629242+00:00
-- url     : https://prove2.me/submissions/abfe3d88-7b13-48f4-9681-bc161c2af43e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_edge_maximal_extension__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7 K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7 L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩