-- Prove2me | solution 2 for WilliamsonShmoys.planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:00:24.55321+00:00
-- url     : https://prove2.me/submissions/84430777-7d65-4902-967b-9b9b940b53ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected)
    (hn : Nat.le 3 (Fintype.card V)) :
    Exists fun (J : SimpleGraph V) =>
      Exists fun (dJ : DecidableRel J.Adj) =>
        And (H ≤ J)
          (And (H ≠ J) (WilliamsonShmoys.HasPlanarDrawingOn J)) := by
  obtain ⟨J, hHJ, hconn, hJ⟩ :=
    WilliamsonShmoys.exists_connected_planar_supergraph H hH hn
  refine ⟨J, Classical.decRel J.Adj, hHJ, ?_, hJ⟩
  intro heq
  subst heq
  exact hDisconnected hconn
