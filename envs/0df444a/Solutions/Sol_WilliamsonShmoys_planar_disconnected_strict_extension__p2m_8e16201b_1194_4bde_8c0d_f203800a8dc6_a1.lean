-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:27:36.191751+00:00
-- url     : https://prove2.me/submissions/0bb8849a-93d8-484e-ba16-5a9f6d1f0aa1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2

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
  classical
  obtain ⟨u, v, hSep, hLe, hNe⟩ :=
    WilliamsonShmoys.disconnected_pair_edge_strict_extension__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
      H hDisconnected hn
  let J : SimpleGraph V := H ⊔ SimpleGraph.edge u v
  let dJ : DecidableRel J.Adj := Classical.decRel _
  refine ⟨J, dJ, ?_, ?_, ?_⟩
  · simpa [J] using hLe
  · simpa [J] using hNe
  · simpa [J] using
      WilliamsonShmoys.planar_add_edge_between_unreachable__p2m_583909d6_9a92_4051_aa1a_1f45dfd3ea8e_a2
        H u v hSep hH