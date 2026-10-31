-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:48.280994+00:00
-- url     : https://prove2.me/submissions/2961b964-1aa5-4412-b9e9-4995272855e0

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) : 3 * Fintype.card V - 6 ≤ S.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026 S hS hCard hMax
