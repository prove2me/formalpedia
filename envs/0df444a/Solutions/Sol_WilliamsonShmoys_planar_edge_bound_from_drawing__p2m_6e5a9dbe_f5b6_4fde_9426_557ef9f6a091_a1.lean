-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:09.18705+00:00
-- url     : https://prove2.me/submissions/d20606af-5ee7-4a51-bc93-6aeac34233f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
      K hcard hconn hK
  have hconnL : L.Connected := hconn.mono hKL
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_da4fb518_365b_4370_9ab7_15c5771178a5_a1
      L hcard hconnL hL hmax
  calc
    K.edgeFinset.card + 6 <= L.edgeFinset.card + 6 :=
      Nat.add_le_add_right (Finset.card_le_card (SimpleGraph.edgeFinset_mono hKL)) 6
    _ <= 3 * Fintype.card V := hbound