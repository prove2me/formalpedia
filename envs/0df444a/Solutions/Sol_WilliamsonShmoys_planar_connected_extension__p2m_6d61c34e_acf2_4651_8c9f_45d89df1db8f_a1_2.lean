-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:12.932799+00:00
-- url     : https://prove2.me/submissions/b11553b4-5648-4d59-9167-1fab5fd9765a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 1 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C, hGC, ⟨-, hC⟩, hconnC⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension L
    (fun H => L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) ⟨le_rfl, hplanar⟩ (by
      rintro H - ⟨hGH, hH⟩ hnc
      haveI : Nonempty V := hne
      obtain ⟨a, b, hab⟩ : ∃ a b, ¬ H.Reachable a b := by
        by_contra hc
        push_neg at hc
        exact hnc ⟨hc⟩
      obtain ⟨K, hHK, hK⟩ := WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 H hH a b hab
      exact ⟨K, hHK, hGH.trans hHK.le, hK⟩)
  exact ⟨C, hGC, hC, hconnC⟩
