-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_of_disconnected_of_card_ge_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:20:24.743039+00:00
-- url     : https://prove2.me/submissions/96b2403d-7187-49cb-be2b-20a44e582193
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ≠ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v : V, ¬ K.Reachable u v := by
    by_contra hn
    apply hconn
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact ⟨fun u v => by
      by_contra hnot
      exact hn ⟨u, v, hnot⟩⟩
  exact WilliamsonShmoys.planar_add_edge_between_components K hK u v huv