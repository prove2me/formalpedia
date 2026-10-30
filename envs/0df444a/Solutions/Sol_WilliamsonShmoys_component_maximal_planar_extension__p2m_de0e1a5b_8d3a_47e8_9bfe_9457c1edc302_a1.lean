-- Prove2me | solution 1 for WilliamsonShmoys.component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:21:53.640005+00:00
-- url     : https://prove2.me/submissions/ebfe6f23-d982-4e71-9ccc-48d0487f8e03

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype C.supp] :
    ∃ M : SimpleGraph C.supp,
      C.toSimpleGraph.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph C.supp, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) := by
  exact WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
    C.toSimpleGraph
    (WilliamsonShmoys.component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
      L hL C)