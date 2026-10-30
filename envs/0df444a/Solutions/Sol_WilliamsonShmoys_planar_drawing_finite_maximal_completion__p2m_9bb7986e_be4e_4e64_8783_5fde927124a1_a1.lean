-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:17.380989+00:00
-- url     : https://prove2.me/submissions/fba19be9-4787-4490-b713-1e7e543eb547

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hStep : ∀ (K : SimpleGraph V), G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ K' : SimpleGraph V,
        K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧ K' ≠ K) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_6932dd3a_aa87_467b_ad6b_7c92eed114e6_a1 G hG
  have hconn : H.Connected := by
    by_contra hn
    obtain ⟨K', hHK', hK', hK'ne⟩ := hStep H hGH hH hn
    exact hK'ne (hmax K' hHK' hK')
  exact ⟨H, hGH, hH, hconn, Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)⟩