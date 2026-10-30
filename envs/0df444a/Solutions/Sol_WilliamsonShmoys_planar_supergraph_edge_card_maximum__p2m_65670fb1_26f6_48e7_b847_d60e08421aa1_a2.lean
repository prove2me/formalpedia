-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_card_maximum__p2m_65670fb1_26f6_48e7_b847_d60e08421aa1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:04:27.711442+00:00
-- url     : https://prove2.me/submissions/4cef16ba-cf90-4f6d-b41e-2c826318b8b3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.edgeSet.ncard = n
  have hnonempty : ∃ n, P n := by
    exact ⟨G.edgeSet.ncard, G, le_rfl, hG, rfl⟩
  have hbounded : ∀ n, P n → n ≤ Nat.choose (Fintype.card V) 2 := by
    intro n hn
    rcases hn with ⟨H, _, _, hn⟩
    rw [← hn]
    exact WilliamsonShmoys.simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1 H
  obtain ⟨n, hn, hmax⟩ :=
    WilliamsonShmoys.exists_maximum_of_bounded_nat_predicate__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
      P (Nat.choose (Fintype.card V) 2) hbounded hnonempty
  rcases hn with ⟨H, hGH, hH, hnH⟩
  refine ⟨H, hGH, hH, ?_⟩
  intro K hGK hK
  have hKn : K.edgeSet.ncard ≤ n :=
    hmax K.edgeSet.ncard ⟨K, hGK, hK, rfl⟩
  simpa [hnH] using hKn
