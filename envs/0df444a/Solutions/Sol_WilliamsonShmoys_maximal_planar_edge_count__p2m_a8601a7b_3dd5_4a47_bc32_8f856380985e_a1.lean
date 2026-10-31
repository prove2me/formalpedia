-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a8601a7b_3dd5_4a47_bc32_8f856380985e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:46.804189+00:00
-- url     : https://prove2.me/submissions/62fa4254-9897-44fe-8c0e-b2e3fc22ecb7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hSub, hPlanar, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_4553358e_4865_4072_b187_cda5e04dbc8a_a2
      H hV hH
  have hEq : J = H := hMax J hSub hPlanar
  cases hEq
  exact hCount