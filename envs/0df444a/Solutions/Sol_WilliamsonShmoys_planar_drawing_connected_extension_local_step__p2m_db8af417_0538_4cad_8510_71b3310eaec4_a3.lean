-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_local_step__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:58:51.098988+00:00
-- url     : https://prove2.me/submissions/7af18a68-2261-496c-bb0a-30195a5901da

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V),
        HasPlanarDrawingOn G →
        ¬ G.Connected →
        ∃ H : SimpleGraph V,
          G ≤ H ∧ H ≠ G ∧ HasPlanarDrawingOn H) := by
  intro h
  let p : Empty → ℝ × ℝ := fun v => v.elim
  let arc : Empty → Empty → ℝ → ℝ × ℝ := fun v => v.elim
  have hdrawing : HasPlanarDrawingOn (⊥ : SimpleGraph Empty) := by
    refine ⟨p, arc, ?_, ?_, ?_⟩
    · intro u v huv
      exact u.elim
    · intro u v huv
      exact u.elim
    · intro u v x y huv hxy huvG hxyG hne t ht s hs heq
      exact u.elim
  have hdisconnected : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact v.elim
  obtain ⟨H, hle, hne, hdraw⟩ :=
    h (V := Empty) (G := (⊥ : SimpleGraph Empty)) hdrawing hdisconnected
  exact hne (Subsingleton.elim H ⊥)