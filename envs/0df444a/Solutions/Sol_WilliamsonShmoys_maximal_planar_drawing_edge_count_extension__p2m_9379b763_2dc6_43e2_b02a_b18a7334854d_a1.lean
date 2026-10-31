-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:36.324256+00:00
-- url     : https://prove2.me/submissions/4ae2087b-2ac0-40b4-84df-748a7d5601cd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hdef : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, M < K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hMK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4 M hM
  have hKbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4 K hK hV hmax
  have hne : M ≠ K := by
    intro heq
    subst K
    omega
  have hlt : M < K := lt_of_le_of_ne hMK hne
  exact ⟨K, hlt, hK⟩