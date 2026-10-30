-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:04.927107+00:00
-- url     : https://prove2.me/submissions/5a48fcf1-3aa4-4d4e-93a6-2a2804c7dc25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hKMax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1 N hN
  have hKN : K.edgeSet = N.edgeSet := hMax K hNK hK
  have hEq :=
    WilliamsonShmoys.maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1 K hK hKMax hCard
  simpa [hKN] using hEq.le