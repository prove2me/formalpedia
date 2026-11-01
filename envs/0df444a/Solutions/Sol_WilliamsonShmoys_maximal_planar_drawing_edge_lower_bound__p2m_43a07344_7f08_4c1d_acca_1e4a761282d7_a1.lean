-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_43a07344_7f08_4c1d_acca_1e4a761282d7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:32.578434+00:00
-- url     : https://prove2.me/submissions/2e6d15e3-0cf6-4372-b088-b5d347c4e837

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1
      M hM hcard
  have hNM : N = M := hmax N hMN hN
  subst N
  omega