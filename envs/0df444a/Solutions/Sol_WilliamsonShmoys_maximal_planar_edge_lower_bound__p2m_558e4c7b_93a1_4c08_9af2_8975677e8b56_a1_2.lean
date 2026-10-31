-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:39:36.092391+00:00
-- url     : https://prove2.me/submissions/9ed196db-687a-4f8f-9c6a-4e764e9a5d06

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edgeSet_ncard_ge

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_drawingOn_edgeSet_ncard_ge L hL hCard hmax
