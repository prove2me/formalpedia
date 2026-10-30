-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:44:51.426246+00:00
-- url     : https://prove2.me/submissions/25781db4-1a2e-4db1-a122-9e51b0f58c5a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hDisc : ¬ G.Connected),
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet) := by
  intro h
  have hd : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph (Fin 0)) :=
    ⟨fun v => v.elim0, fun u => u.elim0, fun a => a.elim0, fun u => u.elim0, fun u => u.elim0⟩
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨H, -, -, hH⟩ := h (⊥ : SimpleGraph (Fin 0)) hd hnc
  obtain ⟨e, he, -⟩ := Set.exists_of_ssubset hH
  induction e using Sym2.ind with
  | _ a b => exact a.elim0
