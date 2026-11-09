-- Prove2me | solution 1 for WilliamsonShmoys.connected_extension_of_pairwise_bridge_closure__p2m_596e37ff_bf61_48b7_90c3_a4814329de9c_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:38.2517+00:00
-- url     : https://prove2.me/submissions/085d439e-24d7-4f4e-b3bb-80a4961eb803

import Mathlib

set_option autoImplicit false

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : P K) (hstep : ∀ (G : SimpleGraph V), (dG : DecidableRel G.Adj) → P G → ∀ u v, ¬ G.Reachable u v → ∃ H : SimpleGraph V, (∀ a b, H.Adj a b ↔ G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧ P H), ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) (fun _ => True) ⊥ (fun a => a.elim0) trivial (fun _ _ _ u => u.elim0)
  exact key H (by tauto)

#print axioms solution
