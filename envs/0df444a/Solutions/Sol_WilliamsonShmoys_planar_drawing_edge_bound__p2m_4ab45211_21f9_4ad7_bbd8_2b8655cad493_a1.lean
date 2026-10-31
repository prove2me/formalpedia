-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:59.892301+00:00
-- url     : https://prove2.me/submissions/33b019e3-1092-4ca3-b007-61530dbb65e4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V), HasPlanarDrawingOn G →
      3 * Fintype.card V ≤ G.edgeSet.ncard + 6) := by
  intro h
  let G : SimpleGraph (Fin 3) := ⊥
  have hDraw : HasPlanarDrawingOn G := by
    refine ⟨fun i => ((i.val : ℝ), (0 : ℝ)), fun _ _ _ => (0, 0), ?_, ?_, ?_⟩
    · intro i j hij
      have hval : (i.val : ℝ) = (j.val : ℝ) := by
        simpa using congrArg Prod.fst hij
      apply Fin.ext
      exact_mod_cast hval
    · intro u v huv hadj
      simp [G] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne
      simp [G] at hadj₁
  have hbad := h G hDraw
  norm_num [G, SimpleGraph.edgeSet] at hbad