-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:54.153129+00:00
-- url     : https://prove2.me/submissions/3da5660e-2688-451f-82bd-5695dde657c4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : WilliamsonShmoys.HasPlanarDrawingOn K), ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) ⊥ (fun a => a.elim0) hdraw
  exact key H (by tauto)

#print axioms solution
