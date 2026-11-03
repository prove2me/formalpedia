-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:23:03.488645+00:00
-- url     : https://prove2.me/submissions/7fb19f2c-ebad-4754-a4c7-bc63a7679d7e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_with_euler_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ 3 * Fintype.card V = N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_supergraph_with_euler_edge_count M hcard hplanar