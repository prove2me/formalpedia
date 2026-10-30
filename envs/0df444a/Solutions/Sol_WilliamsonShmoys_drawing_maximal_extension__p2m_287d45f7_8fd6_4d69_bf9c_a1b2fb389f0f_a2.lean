-- Prove2me | solution 1 for WilliamsonShmoys.drawing_maximal_extension__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:43:34.480513+00:00
-- url     : https://prove2.me/submissions/91137e4d-0fe7-4d22-a8d9-ba0bef8ecd6f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨H, hKH, hmax⟩ :=
    hSfinite.exists_le_maximal (a := K) (show K ∈ S from ⟨le_rfl, hK⟩)
  have hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H := hmax.1.2
  have hKHedges : K.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hKH
  refine ⟨H, hKH, Set.ncard_mono hKHedges, hHdraw, ?_⟩
  intro J hHJ hJ
  have hJmem : J ∈ S := ⟨hKH.trans hHJ, hJ⟩
  exact hmax.2 hJmem hHJ