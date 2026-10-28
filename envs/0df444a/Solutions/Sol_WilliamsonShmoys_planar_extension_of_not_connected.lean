-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_of_not_connected
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:43:11.101334+00:00
-- url     : https://prove2.me/submissions/b492e982-4acb-4a2a-bb3d-4404c7a52fcf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (H : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn H →
        ¬ H.Connected →
        ∃ K : SimpleGraph V,
          H ≤ K ∧ K ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K) := by
  classical
  intro h
  let G : SimpleGraph Empty := ⊥
  have hG : WilliamsonShmoys.HasPlanarDrawingOn G := by
    refine ⟨(fun x : Empty => nomatch x), (fun u : Empty => nomatch u), ?_, ?_, ?_⟩
    · intro u v huv
      cases u
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      cases u
  have hnc : ¬ G.Connected := by
    simp [G, SimpleGraph.connected_bot_iff]
  obtain ⟨K, _, hne, _⟩ := h (V := Empty) G hG hnc
  have hKG : K = G := Subsingleton.elim _ _
  exact hne hKG