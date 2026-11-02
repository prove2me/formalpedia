-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:49:35.807697+00:00
-- url     : https://prove2.me/submissions/9a0ea6ce-1f77-40b3-a37c-0c153caf14f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by
  obtain ⟨K, dK, hHK, hKplanar, hKcard⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
      H hH hcard
  letI : DecidableRel K.Adj := dK
  have hKH : K ≤ H := hmax K hKplanar hHK
  have hmono := WilliamsonShmoys.edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1 K H hKH
  omega