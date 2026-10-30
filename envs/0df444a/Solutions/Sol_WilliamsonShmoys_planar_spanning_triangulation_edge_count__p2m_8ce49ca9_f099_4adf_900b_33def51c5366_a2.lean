-- Prove2me | solution 1 for WilliamsonShmoys.planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:37.353184+00:00
-- url     : https://prove2.me/submissions/9d0c18de-b31d-4837-8802-dc1245e31cdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
import Theorems.Thm_WilliamsonShmoys_finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let b : Nat := 3 * Fintype.card V - 6
  have hBound : ∀ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H → H.edgeSet.ncard ≤ b := by
    intro H hH
    simpa [b] using
      WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
        H hH hV
  have hStep : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H.edgeSet.ncard < b →
      ∃ K : SimpleGraph V, H ≤ K ∧
        K.edgeSet.ncard = H.edgeSet.ncard + 1 ∧
        WilliamsonShmoys.HasPlanarDrawingOn K := by
    intro H hLH hH hlt
    simpa [b] using
      WilliamsonShmoys.planar_drawing_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
        H hV hH hlt
  obtain ⟨M, hLM, hMDraw, hMCard⟩ :=
    WilliamsonShmoys.finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
      L b hDraw hBound hStep
  exact ⟨M, hLM, hMDraw, by simpa [b] using hMCard⟩