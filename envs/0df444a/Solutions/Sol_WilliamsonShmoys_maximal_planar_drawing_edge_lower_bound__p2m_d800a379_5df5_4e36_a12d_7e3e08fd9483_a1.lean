-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:13:28.089731+00:00
-- url     : https://prove2.me/submissions/2746d269-b2c3-4c46-8c0a-6303193dfa28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1 K hK hV
  have hSame := hmax L hKL hL
  have hCard : K.edgeSet.ncard = L.edgeSet.ncard := by rw [hSame]
  omega