-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:12.201574+00:00
-- url     : https://prove2.me/submissions/d465c16d-5150-4cd2-afb2-2bc68d0f0741

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun X =>
      G ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X
  have hS : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHS, hmax⟩ :=
    Finset.exists_max_image S (fun X => X.edgeSet.ncard) hS
  have hGmem : G ∈ S := by
    simp [S, hG]
  have hGH : G ≤ H := (Finset.mem_filter.mp hHS).2.1
  have hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHS).2.2
  refine ⟨H, hGH, ?_, hHdraw, ?_⟩
  · exact hmax G hGmem
  · intro K hHK hKdraw
    have hKmem : K ∈ S := by
      simp [S, hGH.trans hHK, hKdraw]
    by_contra hKH
    have hss : H.edgeSet ⊂ K.edgeSet := by
      rw [SimpleGraph.edgeSet_ssubset_edgeSet]
      exact ⟨hHK, hKH⟩
    have hlt : H.edgeSet.ncard < K.edgeSet.ncard :=
      Set.ncard_lt_ncard hss (Set.toFinite K.edgeSet)
    exact (not_lt_of_ge (hmax K hKmem)) hlt
