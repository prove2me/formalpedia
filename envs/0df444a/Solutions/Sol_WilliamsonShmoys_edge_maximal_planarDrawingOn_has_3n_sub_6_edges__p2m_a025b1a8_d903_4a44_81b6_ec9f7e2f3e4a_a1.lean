-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:00.871502+00:00
-- url     : https://prove2.me/submissions/a2f8d249-0156-4a02-ad5b-b53e8417b9fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V)
    (hmaximal : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; H.edgeFinset ⊆ K.edgeFinset) →
      HasPlanarDrawingOn K →
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset)) :
    (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  have hu := WilliamsonShmoys.edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
    H dH hH hn
  have hl := WilliamsonShmoys.edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
    H dH hH hn hmaximal
  omega