-- Prove2me | solution 2 for WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:06.715311+00:00
-- url     : https://prove2.me/submissions/30f13037-5334-40b4-884a-5b000fdc426d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V), HasPlanarDrawingOn H → ¬ H.Connected →
      ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ ¬ G ≤ H) := by
  intro h
  let H : SimpleGraph Empty := ⊥
  have hdraw : HasPlanarDrawingOn H := by
    refine ⟨(fun x : Empty => x.elim), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro x y heq
      cases x
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy hadju hadjxy hne t ht s hs heq
      cases u
  have hdisc : ¬ H.Connected := by
    simp [H, SimpleGraph.connected_bot_iff]
  obtain ⟨G, _hHG, _hGdraw, hNotGH⟩ := h (V := Empty) H hdraw hdisc
  have hGH : G ≤ H := by
    intro u v hadj
    cases u
  exact hNotGH hGH