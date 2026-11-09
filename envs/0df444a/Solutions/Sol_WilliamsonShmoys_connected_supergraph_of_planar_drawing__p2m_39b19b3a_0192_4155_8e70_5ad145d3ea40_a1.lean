-- Prove2me | solution 1 for WilliamsonShmoys.connected_supergraph_of_planar_drawing__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:52:40.563947+00:00
-- url     : https://prove2.me/submissions/c7388887-7ec3-4c5b-b824-b573a499d175

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

-- The target is elaborated inside namespace `WilliamsonShmoys`; the empty block registers it for `open`.
namespace WilliamsonShmoys
end WilliamsonShmoys

open WilliamsonShmoys in
theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N), ∃ H : SimpleGraph V, N ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ N.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  intro claimed
  -- V = Fin 0: every hypothesis holds vacuously, but no graph on Fin 0 is connected.
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun i => i.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have key : ∀ G : SimpleGraph (Fin 0), ¬ G.Connected := fun G h => h.nonempty.elim fun x => x.elim0
  obtain ⟨H, hH⟩ := claimed (V := Fin 0) ⊥ hdraw
  exact key H (by tauto)

#print axioms solution
