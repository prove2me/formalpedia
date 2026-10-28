-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_extension
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:38:29.691876+00:00
-- url     : https://prove2.me/submissions/a142561b-5397-4c03-9dfa-39b5dbf995bf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem fin0_draw (G : SimpleGraph (Fin 0)) : HasPlanarDrawingOn G :=
  ⟨fun w => w.elim0, fun _ _ _ => 0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (A : SimpleGraph V)
    (hA : WilliamsonShmoys.HasPlanarDrawingOn A)
    (hdisconnected : ¬ A.Connected),
    ∃ B : SimpleGraph V,
      A ≤ B ∧
      WilliamsonShmoys.HasPlanarDrawingOn B ∧
      A.edgeSet.ncard < B.edgeSet.ncard) := by
  intro h
  obtain ⟨B, -, -, hB⟩ := h (⊥ : SimpleGraph (Fin 0)) (fin0_draw _)
    (fun hc => hc.nonempty.elim fun a => a.elim0)
  have : B.edgeSet = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun e => Sym2.ind (fun a _ => a.elim0) e
  rw [this] at hB
  simp at hB
