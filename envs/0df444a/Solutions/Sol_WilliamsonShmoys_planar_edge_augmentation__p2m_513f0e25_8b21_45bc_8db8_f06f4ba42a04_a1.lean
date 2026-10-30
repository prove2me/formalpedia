-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:01:44.434119+00:00
-- url     : https://prove2.me/submissions/2c018fdd-0d31-4603-b4a7-edc1455da1f5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension_exists__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hGap : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension_exists__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
      L hL
  by_cases hEq : L = M
  · have hCount :=
      WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
        M hM hCard hMax
    have hCountL : 3 * Fintype.card V = L.edgeSet.ncard + 6 := by
      simpa [hEq] using hCount
    omega
  · exact ⟨M, hLM, Ne.symm hEq, hM⟩