-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:30.314195+00:00
-- url     : https://prove2.me/submissions/f1fc9bd0-58ac-4477-ba49-6beaf1fb93ba

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hne : 0 < Fintype.card V)
    (hbridge : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ K.Reachable u v ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj
         letI : DecidableRel H.Adj := Classical.decRel H.Adj
         G.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let p : SimpleGraph V → Prop := fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hp : ∃ K : SimpleGraph V, p K := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hDecH, hmax⟩ := (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  have hHprop : p H := hmax.1
  have hHconn : H.Connected := by
    by_contra hnot
    obtain ⟨L, hHL, hLdraw, u, v, hnreach, hLadj⟩ :=
      hbridge H hHprop.1 hHprop.2 hnot
    have hLprop : p L := ⟨hHprop.1.trans hHL, hLdraw⟩
    have hHneL : H ≠ L := by
      intro heq
      subst L
      exact hnreach hLadj.reachable
    have hstrict : H < L := lt_of_le_of_ne hHL hHneL
    have hcard : H.edgeFinset.card < L.edgeFinset.card := by
      letI : DecidableRel H.Adj := hDecH
      exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
    have hmaxL : L.edgeFinset.card ≤ H.edgeFinset.card := by
      letI : DecidableRel H.Adj := hDecH
      exact hmax.2 hLprop
    omega
  refine ⟨H, hHprop.1, hHconn, hHprop.2, ?_⟩
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHprop.1)