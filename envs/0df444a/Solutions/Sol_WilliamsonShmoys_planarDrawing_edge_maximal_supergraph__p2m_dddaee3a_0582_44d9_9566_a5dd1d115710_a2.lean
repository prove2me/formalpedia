-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:13:36.336245+00:00
-- url     : https://prove2.me/submissions/e6889a01-445d-4a08-86a6-14a1448d60d0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ H : SimpleGraph V,
          M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M := by
  classical
  obtain ⟨M, hKM, hM, hmax⟩ :=
    finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1
      (P := fun G : SimpleGraph V => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      ⟨le_refl K, hK⟩
  refine ⟨M, hKM, hM.2, ?_⟩
  intro H hMH hH
  exact hmax H hMH ⟨le_trans hKM hMH, hH⟩