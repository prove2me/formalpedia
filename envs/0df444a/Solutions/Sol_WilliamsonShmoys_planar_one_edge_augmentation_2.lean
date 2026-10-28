-- Prove2me | solution 2 for WilliamsonShmoys.planar_one_edge_augmentation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:45:27.30504+00:00
-- url     : https://prove2.me/submissions/62356a8e-7c5a-4de7-a3b4-0f236fc1c67d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected),
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard < N.edgeSet.ncard) := by
  intro h
  obtain ⟨B, -, -, hB⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  have : B.edgeSet = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun e => Sym2.ind (fun a _ => a.elim0) e
  rw [this] at hB
  simp at hB
