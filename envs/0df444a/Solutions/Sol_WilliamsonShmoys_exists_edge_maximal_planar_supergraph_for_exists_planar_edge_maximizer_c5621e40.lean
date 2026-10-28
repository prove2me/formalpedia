-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:55:08.336626+00:00
-- url     : https://prove2.me/submissions/efe79aca-4cc5-4114-95cc-77cb7f934f2d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hCandidates : candidates.Nonempty := by
    refine ⟨G, ?_⟩
    simp [candidates, hDrawing]
  obtain ⟨H, hHmem, hMax⟩ :=
    Finset.exists_max_image candidates (fun K => K.edgeSet.ncard) hCandidates
  have hH := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hH.1, hH.2, ?_, ?_⟩
  · have hGmem : G ∈ candidates := by simp [candidates, hDrawing]
    exact hMax G hGmem
  · intro K hHK hKDrawing
    have hKmem : K ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans hH.1 hHK, hKDrawing⟩
    have hEdges : H.edgeSet = K.edgeSet :=
      Set.eq_of_subset_of_ncard_le (SimpleGraph.edgeSet_mono hHK) (hMax K hKmem)
    exact SimpleGraph.edgeSet_inj.mp hEdges.symm