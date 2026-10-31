-- Prove2me | solution 2 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:01:32.937125+00:00
-- url     : https://prove2.me/submissions/caee575c-915c-449d-8d24-10788c6f5132

import Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_maximal_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_augmentation_to_maximal_edge_count K hCard hK
