-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:14.556547+00:00
-- url     : https://prove2.me/submissions/0bda94d8-28e6-4312-816d-ddbae49ab6e0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hM : P M) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      P T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet → P U →
        U.edgeSet.ncard ≤ T.edgeSet.ncard := by
  classical
  let Q : SimpleGraph V → Prop := fun T => M.edgeSet ⊆ T.edgeSet ∧ P T
  have hbound : ∀ T, Q T → T.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
    intro T _
    exact WilliamsonShmoys.edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2 T
  have hnonempty : ∃ T, Q T := ⟨M, Set.Subset.rfl, hM⟩
  obtain ⟨T, hT, hmax⟩ :=
    WilliamsonShmoys.exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
      Q (fun T => T.edgeSet.ncard) (Fintype.card (Sym2 V)) hbound hnonempty
  refine ⟨T, hmax M ⟨Set.Subset.rfl, hM⟩, hT.1, hT.2, ?_⟩
  intro U hTU hPU
  exact hmax U ⟨Set.Subset.trans hT.1 hTU, hPU⟩