-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:58.163201+00:00
-- url     : https://prove2.me/submissions/aa707cbf-eb80-4545-8556-eb97512aae6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
import Theorems.Thm_finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
      (P := WilliamsonShmoys.HasPlanarDrawingOn) G hG
      (fun {A B} hle hP =>
        WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
          (G := A) (H := B) (hGH := hle) (hH := hP))
  exact ⟨H, hGH, hH, hmax⟩
