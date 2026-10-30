-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:24.708999+00:00
-- url     : https://prove2.me/submissions/c4fbbf39-6669-40b0-9fb8-945a9f990d93

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V),
    WilliamsonShmoys.HasPlanarDrawingOn G →
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) := by
  intro h
  let G : SimpleGraph (Fin 1) := ⊥
  have hDraw : WilliamsonShmoys.HasPlanarDrawingOn G := by
    refine ⟨(fun _ => (0, 0)), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro a b hab
      exact Subsingleton.elim a b
    · intro u v huv hadj
      simp [G] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp [G] at hadj₁
  have hbound := h G hDraw
  norm_num [G] at hbound