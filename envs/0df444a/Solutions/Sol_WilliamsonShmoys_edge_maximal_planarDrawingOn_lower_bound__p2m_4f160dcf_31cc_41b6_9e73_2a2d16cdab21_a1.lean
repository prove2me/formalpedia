-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:53.220921+00:00
-- url     : https://prove2.me/submissions/fa642d6a-de6d-4099-b65c-98ad5e32c7da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
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
    (letI : DecidableRel H.Adj := dH; 3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by
  classical
  letI : DecidableRel H.Adj := dH
  obtain ⟨K, dK, hK, hsub, hcard⟩ :=
    WilliamsonShmoys.edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
      H dH hH hn
  have heq : (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset) :=
    hmaximal K dK hsub hK
  have hbound : 3 * Fintype.card V - 6 = H.edgeFinset.card := by
    calc
      3 * Fintype.card V - 6 = K.edgeFinset.card := hcard.symm
      _ = H.edgeFinset.card := congrArg Finset.card heq
  exact le_of_eq hbound