-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:06:28.611364+00:00
-- url     : https://prove2.me/submissions/d8f03702-a25b-4f5e-a42e-0685af7d3d40

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn G →
        ¬ G.Connected →
        ∃ H : SimpleGraph V,
          G < H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hG : WilliamsonShmoys.HasPlanarDrawingOn G := by
    refine ⟨(fun v : Empty => nomatch v), (fun _ _ _ => (0, 0)), ?_⟩
    constructor
    · intro x y hxy
      exact nomatch x
    · constructor
      · intro u v huv hadj
        exact nomatch u
      · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
        exact nomatch u
  have hDisconnected : ¬ G.Connected := by
    intro hconn
    exact isEmptyElim (Classical.choice hconn.nonempty)
  obtain ⟨H, hGH, hHConnected, hHPlanar⟩ := h G hG hDisconnected
  exact isEmptyElim (Classical.choice hHConnected.nonempty)