-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_component_bridge__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T09:12:27.649518+00:00
-- url     : https://prove2.me/submissions/595deaa9-0072-4848-bf42-39fe2cc37399

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
      (hGnot : ¬ G.Connected),
      ∃ u v : V, ∃ H : SimpleGraph V,
        ¬ G.Adj u v ∧ G ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hDraw : HasPlanarDrawingOn G := by
    unfold HasPlanarDrawingOn
    refine ⟨(fun x : Empty => nomatch x), (fun x y t => nomatch x), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u v huv hAdj
      cases u
    · intro u v x y huv hxy hAdj₁ hAdj₂ hne t ht s hs heq
      cases u
  have hNot : ¬ G.Connected := by
    intro hconn
    rcases hconn.nonempty with ⟨x⟩
    exact nomatch x
  have hResult := h (V := Empty) G hDraw hNot
  rcases hResult with ⟨u, v, H, hEdge⟩
  exact nomatch u
