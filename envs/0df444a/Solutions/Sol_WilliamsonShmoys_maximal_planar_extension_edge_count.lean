-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:23:33.172872+00:00
-- url     : https://prove2.me/submissions/f43acc9e-222d-4b5e-9a6b-46792ed7ff88

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_0d153890
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_0d153890

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_0d153890 K hK
  exact ⟨H, hKH, hH,
    WilliamsonShmoys.maximal_planar_graph_edge_count_0d153890 H hV hH hmax⟩