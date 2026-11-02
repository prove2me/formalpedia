-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentation__p2m_38e6d80b_f3ea_4425_9db3_0bd7e0773f7f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:29:53.952596+00:00
-- url     : https://prove2.me/submissions/422e5955-ce8e-4fa7-afd0-d12879c8f0b4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsmall : H.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧ ¬ J ≤ H := by
  classical
  have hcounts : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [H.edgeSet.ncard_eq_toFinset_card (Set.toFinite _)]
    apply congrArg Finset.card
    ext e
    simp [SimpleGraph.edgeFinset]
  have hsmall' : H.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    rw [hcounts]
    omega
  obtain ⟨J, hstrict, hJdraw⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation
      H hcard hHdraw hsmall'
  exact ⟨J, hstrict.le, hJdraw, not_le_of_gt hstrict⟩
