-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:43:08.495098+00:00
-- url     : https://prove2.me/submissions/1d33fa40-10f8-4351-8744-c1f22fb84676

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G), ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H) := by
  intro claimed
  -- V = Fin 0: ⊥ is drawable, but no graph on an empty type is connected.
  have hdraw : HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  obtain ⟨H, _, hH, _⟩ := claimed (⊥ : SimpleGraph (Fin 0)) hdraw
  exact hH.nonempty.elim fun x => x.elim0

#print axioms solution
