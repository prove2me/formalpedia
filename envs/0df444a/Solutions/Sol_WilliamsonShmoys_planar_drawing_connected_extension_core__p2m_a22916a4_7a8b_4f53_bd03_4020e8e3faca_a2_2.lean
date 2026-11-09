-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_a22916a4_7a8b_4f53_bd03_4020e8e3faca_a2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:53.024166+00:00
-- url     : https://prove2.me/submissions/ee4c591c-ba5f-4911-874f-8a2dabf6b6cb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H), ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) ⊥ hdraw
  exact key H (by tauto)

#print axioms solution
