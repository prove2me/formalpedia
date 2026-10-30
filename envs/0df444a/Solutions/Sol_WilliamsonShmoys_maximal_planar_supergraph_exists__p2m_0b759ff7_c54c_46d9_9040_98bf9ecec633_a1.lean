-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:39.959631+00:00
-- url     : https://prove2.me/submissions/ca6e76d0-cc1f-436b-ab90-34c2a55d9bc8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by
  classical
  obtain ⟨H, hGH, hHd, hmax⟩ :=
    WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2 G hG
  refine ⟨H, hGH, hHd, ?_⟩
  intro K hHK hKd
  have hEq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le hHK (hmax K hHK hKd)
  rw [hEq]