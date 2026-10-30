-- Prove2me | solution 1 for WilliamsonShmoys.planar_one_edge_insertion__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:21.414319+00:00
-- url     : https://prove2.me/submissions/6de9c8bf-93a0-460a-bc8e-ac24a273afb3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V),
        HasPlanarDrawingOn G →
        ¬ G.Connected →
        ∃ K : SimpleGraph V,
          G ≤ K ∧ HasPlanarDrawingOn K ∧
          G.edgeSet.ncard < K.edgeSet.ncard) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hG : HasPlanarDrawingOn G := by
    refine ⟨(fun v : Empty => v.elim), (fun u : Empty => u.elim), ?_, ?_, ?_⟩
    · intro a b hab
      exact a.elim
    · intro u v
      exact u.elim
    · intro u v x y
      exact u.elim
  have hdisconnected : ¬ G.Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact v.elim
  obtain ⟨K, _, _, hlt⟩ := h (G := G) hG hdisconnected
  have hK : K = (⊥ : SimpleGraph Empty) := by
    ext u v
    exact u.elim
  have hzero : K.edgeSet.ncard = 0 := by
    simp [hK]
  rw [hzero] at hlt
  omega