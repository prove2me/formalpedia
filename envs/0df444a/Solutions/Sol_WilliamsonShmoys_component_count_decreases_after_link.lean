-- Prove2me | solution 1 for WilliamsonShmoys.component_count_decreases_after_link
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:53:38.575372+00:00
-- url     : https://prove2.me/submissions/38ab7bfe-497b-4871-8e21-fadb99503850

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (Y Z : SimpleGraph V)
    (iY : Fintype Y.ConnectedComponent)
    (hYZ : Y ≤ Z)
    (u v : V)
    (hNotReachable : ¬ Y.Reachable u v)
    (hLink : Z.Adj u v) :
    ∃ (iZ : Fintype Z.ConnectedComponent),
      @Fintype.card Z.ConnectedComponent iZ <
        @Fintype.card Y.ConnectedComponent iY := by
  classical
  let f : Y.ConnectedComponent → Z.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hYZ)
  have hsurj : Function.Surjective f := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h w => exact ⟨Y.connectedComponentMk w, rfl⟩
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have : Y.connectedComponentMk u = Y.connectedComponentMk v := by
      apply hinj
      simp only [f, SimpleGraph.ConnectedComponent.map_mk]
      exact SimpleGraph.ConnectedComponent.eq.mpr hLink.reachable
    exact hNotReachable (SimpleGraph.ConnectedComponent.eq.mp this)
  let iZ : Fintype Z.ConnectedComponent := Fintype.ofSurjective f hsurj
  exact ⟨iZ, Fintype.card_lt_of_surjective_not_injective f hsurj hninj⟩
