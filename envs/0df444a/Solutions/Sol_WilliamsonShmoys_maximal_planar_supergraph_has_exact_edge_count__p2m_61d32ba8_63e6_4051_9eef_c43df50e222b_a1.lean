-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_has_exact_edge_count__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:36.31953+00:00
-- url     : https://prove2.me/submissions/12d0907e-c7fa-400c-8932-44a849551d15

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hKL : K <= L)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, K <= M -> WilliamsonShmoys.HasPlanarDrawingOn M ->
      M.edgeSet.ncard <= L.edgeSet.ncard) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
      L hCard hDraw
  let hExt :=
    WilliamsonShmoys.planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
      L hCard hDraw
  let M := Classical.choose hExt
  have hExtSpec := Classical.choose_spec hExt
  have hLM : L <= M := hExtSpec.1
  have hMDraw : WilliamsonShmoys.HasPlanarDrawingOn M := hExtSpec.2.1
  have hMCard : M.edgeSet.ncard = 3 * Fintype.card V - 6 := hExtSpec.2.2
  have hML := hMax M (hKL.trans hLM) hMDraw
  rw [hMCard] at hML
  omega