-- Prove2me | solution 1 for WilliamsonShmoys.component_count_strictly_decreases_of_cross_edge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:39:56.111334+00:00
-- url     : https://prove2.me/submissions/555a73b4-ed1b-4c26-91ce-fbfa16b2a612

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G K : SimpleGraph V) (hGK : G ≤ K)
    (u v : V) (hnot : ¬ G.Reachable u v) (hadj : K.Adj u v) :
    Nat.card K.ConnectedComponent < Nat.card G.ConnectedComponent := by
  classical
  let f : G.ConnectedComponent → K.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hGK)
  have hsurj : Function.Surjective f := by
    simpa [f] using SimpleGraph.ConnectedComponent.surjective_map_ofLE hGK
  have hninj : ¬ Function.Injective f := by
    intro hinj
    apply hnot
    apply SimpleGraph.ConnectedComponent.exact
    apply hinj
    simpa [f] using
      (SimpleGraph.ConnectedComponent.sound (G := K) hadj.reachable)
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_surjective_not_injective f hsurj hninj)