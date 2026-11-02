-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:32.591719+00:00
-- url     : https://prove2.me/submissions/062351ec-c9a9-4e01-85e3-6055dffce13d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) := by
  intro h
  let p : Empty → ℝ × ℝ := fun x => nomatch x
  let arc : Empty → Empty → ℝ → ℝ × ℝ := fun x => nomatch x
  have hdraw : HasPlanarDrawingOn (⊥ : SimpleGraph Empty) := by
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro x y _
      exact x.elim
    · intro u v huv hadj
      exact u.elim
    · intro u v x y huv hxy hadj hxy' hed t ht s hs heq
      exact u.elim
  have hdisconnected : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hc
    rcases hc.nonempty with ⟨x⟩
    exact x.elim
  have hresult := h (V := Empty) (G := (⊥ : SimpleGraph Empty)) hdraw hdisconnected
  rcases hresult with ⟨H, hsub, hplanar, u, v, hnot, hadj⟩
  exact u.elim