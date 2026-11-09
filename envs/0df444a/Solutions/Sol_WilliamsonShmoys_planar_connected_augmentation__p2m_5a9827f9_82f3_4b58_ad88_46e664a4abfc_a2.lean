-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_augmentation__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:45.836541+00:00
-- url     : https://prove2.me/submissions/3e369aa3-0742-423a-94a1-896ab0349ba7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M), ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧ M.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) ⊥ hdraw
  exact key H (by tauto)

#print axioms solution
