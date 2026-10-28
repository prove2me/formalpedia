-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_addEdge_progress
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:05.096137+00:00
-- url     : https://prove2.me/submissions/d513e210-a157-4454-b530-588fc9b35bfa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_hP : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph Empty) :=
  ⟨fun v => v.elim, fun v => v.elim, fun v => v.elim, fun u => u.elim, fun u => u.elim⟩

theorem S181_hC : ¬ (⊥ : SimpleGraph Empty).Connected := fun hc => hc.nonempty.elim (fun v => v.elim)

theorem S181_eq (K : SimpleGraph Empty) : K = ⊥ := by
  ext a; exact a.elim

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn G →
    ¬ G.Connected →
    ∃ K : SimpleGraph V,
      G.edgeSet ⊂ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K) := by
  intro h
  obtain ⟨K, hss, -⟩ := h (⊥ : SimpleGraph Empty) S181_hP S181_hC
  rw [S181_eq K] at hss
  exact hss.ne rfl
