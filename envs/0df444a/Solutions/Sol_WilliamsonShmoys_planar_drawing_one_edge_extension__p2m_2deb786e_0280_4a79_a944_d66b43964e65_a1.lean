-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_one_edge_extension__p2m_2deb786e_0280_4a79_a944_d66b43964e65_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:43.541406+00:00
-- url     : https://prove2.me/submissions/5330e702-a7c5-4a82-95e8-4bacb1781ec6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V),
      HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        (∀ u v, G.Adj u v → H.Adj u v) ∧
        (∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) ∧
        HasPlanarDrawingOn H) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hG : HasPlanarDrawingOn G := by
    refine ⟨(fun _ : Empty => (0, 0)), (fun _ _ _ => (0, 0)), ?_⟩
    refine ⟨?_, ?_⟩
    · intro x
      cases x
    · refine ⟨?_, ?_⟩
      · intro u v huv hadj
        cases u
      · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
        cases u
  have hnc : ¬ G.Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact v.elim
  obtain ⟨H, hsup, hedge, hH⟩ := h (V := Empty) G hG hnc
  rcases hedge with ⟨u, v, hnot, hadj⟩
  exact u.elim