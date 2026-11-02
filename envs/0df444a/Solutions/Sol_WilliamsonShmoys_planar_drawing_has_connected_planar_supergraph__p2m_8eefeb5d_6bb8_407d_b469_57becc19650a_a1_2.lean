-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_connected_planar_supergraph__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:56:14.439203+00:00
-- url     : https://prove2.me/submissions/2f5d1317-7748-4a1a-b8ad-df9b8550272d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V),
      HasPlanarDrawingOn G →
      ∃ H : SimpleGraph V,
        (∀ u v, G.Adj u v → H.Adj u v) ∧
        H.Connected ∧ HasPlanarDrawingOn H) := by
  intro h
  let G : SimpleGraph Empty := ⊤
  have hG : HasPlanarDrawingOn G := by
    refine ⟨(fun _ : Empty => (0, 0)), (fun _ _ _ => (0, 0)), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      cases u
  obtain ⟨H, hsub, hconn, hH⟩ := h (V := Empty) G hG
  have hempty : ¬ H.Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact v.elim
  exact hempty hconn