-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_by_edge_card__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:06:23.287014+00:00
-- url     : https://prove2.me/submissions/f29af7c5-2d2c-43b4-bab5-822b84258d01

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      G ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
          G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H →
            H.edgeFinset.card ≤ L.edgeFinset.card := by
  classical
  let S : Finset (SimpleGraph V) :=
    (Finset.univ : Finset (SimpleGraph V)).filter (fun H => G ≤ H ∧ HasPlanarDrawingOn H)
  have hGS : G ∈ S := by simp [S, hG]
  obtain ⟨L, hLS, hLmax⟩ := S.exists_max_image (fun H => H.edgeSet.ncard) ⟨G, hGS⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hLS
  refine ⟨L, Classical.decRel _, hLS.1, hLS.2, ?_⟩
  intro H _ hGH hH
  have := hLmax H (by simp [S, hGH, hH])
  simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  exact this
