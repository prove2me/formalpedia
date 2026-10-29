-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:12:59.521695+00:00
-- url     : https://prove2.me/submissions/ff89d250-7f5e-4753-93ca-31fc3101ce7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
      H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_68514819_a212_4a71_843f_93b3ee5d7783_a2
    K hK hV hmax