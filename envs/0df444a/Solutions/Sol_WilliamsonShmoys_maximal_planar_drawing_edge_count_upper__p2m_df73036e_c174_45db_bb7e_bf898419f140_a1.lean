-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_df73036e_c174_45db_bb7e_bf898419f140_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:04.47111+00:00
-- url     : https://prove2.me/submissions/8b78f41a-e858-4502-a676-223c132f82f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V), HasPlanarDrawingOn H →
    3 ≤ Fintype.card V →
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6) := by
  intro h
  let H : SimpleGraph (Fin 3) := ⊥
  have hDraw : HasPlanarDrawingOn H := by
    refine ⟨fun v => ((v.val : ℝ), 0), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro a b hab
      have hcoord : (a.val : ℝ) = (b.val : ℝ) := congrArg Prod.fst hab
      apply Fin.ext
      exact_mod_cast hcoord
    · intro u v huv hadj
      simp [H] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp [H] at hadj₁
  have hCard : 3 ≤ Fintype.card (Fin 3) := by simp
  have hbad := h H hDraw hCard
  norm_num [H] at hbad