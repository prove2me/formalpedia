-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound_729fc1e5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:35:09.848165+00:00
-- url     : https://prove2.me/submissions/7dc53698-e342-4f7c-8f93-ec90db1fbba1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hRH, hHdraw, hHmax, hRle⟩ :=
    WilliamsonShmoys.maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
      R hR
  have hHbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
      H hV hHdraw hHmax
  exact hRle.trans hHbound