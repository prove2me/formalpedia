-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_2a02a607_0135_4f55_809a_3285938451f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:35.060677+00:00
-- url     : https://prove2.me/submissions/67347f07-0c7d-4a92-83cd-ae8a470e0daf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1 L hL hCard
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1 L hL hCard hmax
  omega
