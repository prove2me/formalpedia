-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:15.012811+00:00
-- url     : https://prove2.me/submissions/cf252236-146d-4a7d-9529-27c3ca198346
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hNM, hM, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
      N hV hN
  exact ⟨M, hNM, hM,
    WilliamsonShmoys.maximal_planar_supergraph_exact_edge_count__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
      M hV hM hMax⟩