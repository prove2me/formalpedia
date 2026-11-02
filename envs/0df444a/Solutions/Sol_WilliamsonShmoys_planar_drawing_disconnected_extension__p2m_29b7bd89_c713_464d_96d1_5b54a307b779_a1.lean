-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:43.859885+00:00
-- url     : https://prove2.me/submissions/6e6c261b-7cd2-4df1-b4ed-401885248cf6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
        (hH : HasPlanarDrawingOn H),
        ¬ H.Connected →
          ∃ u v, ¬ H.Reachable u v ∧
            HasPlanarDrawingOn
              (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)))) := by
  intro h
  have hd : HasPlanarDrawingOn (⊥ : SimpleGraph PEmpty) := by
    unfold HasPlanarDrawingOn
    refine ⟨(fun x : PEmpty => x.elim), (fun x y _ => x.elim), ?_⟩
    constructor
    · intro x
      exact x.elim
    · constructor
      · intro u
        exact u.elim
      · intro u
        exact u.elim
  have hnc : ¬ (⊥ : SimpleGraph PEmpty).Connected := by
    intro hc
    exact hc.nonempty.elim (fun x => x.elim)
  obtain ⟨u, v, _, _⟩ := h (⊥ : SimpleGraph PEmpty) hd hnc
  exact PEmpty.elim u