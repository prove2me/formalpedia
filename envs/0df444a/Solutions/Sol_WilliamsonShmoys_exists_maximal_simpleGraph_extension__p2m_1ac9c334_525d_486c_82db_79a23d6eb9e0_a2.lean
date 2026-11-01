-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:19:20.499318+00:00
-- url     : https://prove2.me/submissions/ef3557a3-e4e3-48cc-895a-6180378ffa7b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      N ≤ M ∧
      P M ∧
      (∀ M' : SimpleGraph V, M ≤ M' → P M' → M' = M) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => N ≤ G ∧ P G
  have hN : N ∈ candidates := by
    simp [candidates, hP]
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeSet.ncard) ⟨N, hN⟩
  have hNM : N ≤ M := (Finset.mem_filter.mp hM).2.1
  have hPM : P M := (Finset.mem_filter.mp hM).2.2
  refine ⟨M, ?_, hNM, hPM, ?_⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hNM)
  · intro M' hMM' hPM'
    have hM' : M' ∈ candidates := by
      simp [candidates, hNM.trans hMM', hPM']
    by_cases heq : M' = M
    · exact heq
    · have hsubset : M.edgeSet ⊆ M'.edgeSet :=
        SimpleGraph.edgeSet_subset_edgeSet.mpr hMM'
      have hssubset : M.edgeSet ⊂ M'.edgeSet := by
        refine ⟨hsubset, ?_⟩
        intro he
        have hM'M : M' ≤ M := SimpleGraph.edgeSet_subset_edgeSet.mp he
        exact heq (le_antisymm hM'M hMM')
      have hlt : M.edgeSet.ncard < M'.edgeSet.ncard :=
        Set.ncard_lt_ncard hssubset
      have hle := hmax M' hM'
      omega