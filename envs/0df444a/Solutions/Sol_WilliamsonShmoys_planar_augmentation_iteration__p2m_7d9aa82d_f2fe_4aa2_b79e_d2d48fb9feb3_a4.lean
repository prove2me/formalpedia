-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a4
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:51:03.733909+00:00
-- url     : https://prove2.me/submissions/93e2ef0d-20fe-4653-bccd-9a1832ce9801

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hstep : ∀ (H : SimpleGraph V), G ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → ¬ H.Connected →
      ∃ (u v : V) (huv : u ≠ v),
        ¬ H.Reachable u v ∧
        ∃ K : SimpleGraph V,
          H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          ∀ a b, K.Adj a b ↔
            H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ C.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn C := by
  obtain ⟨C, hGC, ⟨-, hC⟩, hconn⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension G
    (fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) ⟨le_rfl, hG⟩ (by
      rintro H - ⟨hGH, hH⟩ hnc
      obtain ⟨u, v, huv, hnr, K, hHK, hK, hadj⟩ := hstep H hGH hH hnc
      refine ⟨K, lt_of_le_of_ne hHK ?_, hGH.trans hHK, hK⟩
      intro hEq
      have hKuv : K.Adj u v := (hadj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      rw [← hEq] at hKuv
      exact hnr hKuv.reachable)
  exact ⟨C, hGC, hconn, hC⟩
