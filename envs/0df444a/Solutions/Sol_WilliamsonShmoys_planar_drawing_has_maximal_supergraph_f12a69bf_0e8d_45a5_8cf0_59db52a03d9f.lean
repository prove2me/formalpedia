-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:13:20.433008+00:00
-- url     : https://prove2.me/submissions/d31569bc-f812-4089-b41b-d13d3d5a8062

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hSne : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp [S, hL]
  obtain ⟨H, hHS, hHmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hSne
  have hHmem := Finset.mem_filter.mp hHS
  rcases hHmem with ⟨_, hLH, hHdrawing⟩
  refine ⟨H, hLH, ?_, hHdrawing, ?_⟩
  · exact Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hLH) (Set.toFinite _)
  · intro K hHK hKdrawing
    have hKmem : K ∈ S := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ K, hLH.trans hHK, hKdrawing⟩
    by_contra hne
    have hstrict : H.edgeSet ⊂ K.edgeSet := by
      apply SimpleGraph.edgeSet_ssubset_edgeSet.mpr
      refine ⟨hHK, ?_⟩
      intro hKH
      exact hne (le_antisymm hKH hHK)
    have hcard : H.edgeSet.ncard < K.edgeSet.ncard :=
      Set.ncard_lt_ncard hstrict (Set.toFinite _)
    exact (not_lt_of_ge (hHmax K hKmem)) hcard