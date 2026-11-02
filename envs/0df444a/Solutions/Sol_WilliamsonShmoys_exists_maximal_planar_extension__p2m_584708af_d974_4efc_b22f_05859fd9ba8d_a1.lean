-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:59:08.865278+00:00
-- url     : https://prove2.me/submissions/bd1a2380-d052-4be9-b962-78eb1396b92b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
import Theorems.Thm_WilliamsonShmoys_eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  obtain ⟨H, hGH, hHP, hbase, hmax⟩ :=
    WilliamsonShmoys.exists_planar_extension_max_card__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
      G hG
  refine ⟨H, hGH, hHP, hbase, ?_⟩
  intro K hHK hKP
  apply WilliamsonShmoys.eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1 H K hHK
  exact hmax K (le_trans hGH hHK) hKP