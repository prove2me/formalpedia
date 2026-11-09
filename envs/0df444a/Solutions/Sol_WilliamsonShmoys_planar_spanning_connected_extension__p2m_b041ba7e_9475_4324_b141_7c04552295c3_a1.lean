-- Prove2me | solution 1 for WilliamsonShmoys.planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:56.295723+00:00
-- url     : https://prove2.me/submissions/eccb7e6e-ff9d-4a13-b830-58bd3f79a624

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H), ∃ K : SimpleGraph V, H.edgeSet.ncard ≤ K.edgeSet.ncard ∧ K.Connected ∧ HasPlanarDrawingOn K) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) ⊥ hdraw
  exact key H (by tauto)

#print axioms solution
