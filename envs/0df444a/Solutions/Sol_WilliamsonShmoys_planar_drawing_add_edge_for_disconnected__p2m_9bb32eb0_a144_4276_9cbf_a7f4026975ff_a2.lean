-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_for_disconnected__p2m_9bb32eb0_a144_4276_9cbf_a7f4026975ff_a2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:43:10.429934+00:00
-- url     : https://prove2.me/submissions/6540941a-f4ee-4d1b-a4c9-c4630721a1f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hP : HasPlanarDrawingOn P) (hDisconnected : ¬ P.Connected), ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ ¬ Q ≤ P) := by
  intro claimed
  -- V = Fin 0: ⊥ is drawable and not connected, but every graph on Fin 0 is ≤ ⊥.
  have hdraw : HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun h => h.nonempty.elim fun x => x.elim0
  obtain ⟨Q, _, _, hQ⟩ := claimed (⊥ : SimpleGraph (Fin 0)) hdraw hnc
  exact hQ (by intro v; exact v.elim0)

#print axioms solution
