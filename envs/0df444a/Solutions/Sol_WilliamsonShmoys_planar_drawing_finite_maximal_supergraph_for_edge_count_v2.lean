-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_supergraph_for_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:45:33.702779+00:00
-- url     : https://prove2.me/submissions/86842a05-b94d-4e4b-af06-acd9b9659ad6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K => M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hadmissible : admissible.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hM⟩
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image admissible (fun K => K.edgeFinset.card) hadmissible
  have hNM : M ≤ N := (Finset.mem_filter.mp hNmem).2.1
  have hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N :=
    (Finset.mem_filter.mp hNmem).2.2
  refine ⟨N, hNM, hNdraw, ?_⟩
  intro K hNK hKdraw
  have hKmem : K ∈ admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, le_trans hNM hNK, hKdraw⟩
  have hEdges : N.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hNK
  have hEdgesEq : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hEdges (hNmax K hKmem)
  exact SimpleGraph.edgeFinset_inj.mp hEdgesEq.symm