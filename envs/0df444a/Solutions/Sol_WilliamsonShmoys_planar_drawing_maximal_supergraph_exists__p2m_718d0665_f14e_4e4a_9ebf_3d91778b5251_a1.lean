-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:15.788356+00:00
-- url     : https://prove2.me/submissions/e7f1e4ab-c7a5-495b-ab34-0419db2c5784

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by
  classical
  let P : SimpleGraph V → Prop := fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  let s : Finset (SimpleGraph V) := Finset.univ.filter P
  have hs : s.Nonempty := by
    refine ⟨M, ?_⟩
    simp [s, P, hM]
  obtain ⟨N, hN, hmax⟩ :=
    Finset.exists_max_image s (fun G => G.edgeFinset.card) hs
  have hNP : P N := (Finset.mem_filter.mp hN).2
  refine ⟨N, hNP.1, hNP.2, ?_⟩
  intro K hNK hK
  have hKP : P K := ⟨hNP.1.trans hNK, hK⟩
  have hKmem : K ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ K, hKP⟩
  have hsubset : N.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hNK
  have hcard : K.edgeFinset.card ≤ N.edgeFinset.card := hmax K hKmem
  have hedge : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  have hEq : N = K := (SimpleGraph.edgeFinset_inj).mp hedge
  exact le_of_eq hEq.symm