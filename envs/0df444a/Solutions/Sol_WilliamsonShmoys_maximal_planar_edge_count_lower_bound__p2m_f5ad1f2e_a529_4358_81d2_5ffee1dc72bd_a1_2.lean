-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f5ad1f2e_a529_4358_81d2_5ffee1dc72bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:42:56.228787+00:00
-- url     : https://prove2.me/submissions/bb09154d-c3f7-40ad-9542-aae816a34b8e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; 3 * Fintype.card V ≤ L.edgeFinset.card + 6) :=
  WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_757b64a4_4ecc_451f_8c8e_f98c58cc600e_a1 L hcard hL hmax