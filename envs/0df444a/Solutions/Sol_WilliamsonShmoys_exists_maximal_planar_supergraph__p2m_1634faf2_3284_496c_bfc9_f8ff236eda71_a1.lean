-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:08:16.987905+00:00
-- url     : https://prove2.me/submissions/c1b20439-2f43-4fd6-b672-14adce4bb765

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ HasPlanarDrawingOn G)
  have hKmem : K ∈ S := by
    simp [S, hK]
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeFinset.card) ⟨K, hKmem⟩
  have hLdata : K ≤ L ∧ HasPlanarDrawingOn L :=
    (Finset.mem_filter.mp hLmem).2
  refine ⟨L, hLdata.1, hLdata.2, ?_⟩
  intro M hLM hMd
  have hMmem : M ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hLdata.1.trans hLM, hMd⟩
  have hMmax := hLmax M hMmem
  have hsub : L.edgeFinset ⊆ M.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM
  have heq : L.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hMmax
  exact (SimpleGraph.edgeFinset_inj.mp heq).symm
