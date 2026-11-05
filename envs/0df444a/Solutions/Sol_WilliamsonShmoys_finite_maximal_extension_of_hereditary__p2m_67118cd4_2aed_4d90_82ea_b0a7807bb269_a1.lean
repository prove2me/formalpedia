-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:18:31.156999+00:00
-- url     : https://prove2.me/submissions/44256861-93ca-4d81-9dcb-c19be22cabad

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ {G H : SimpleGraph V}, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet → P K → K.edgeSet = M.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun M => P M ∧ N.edgeSet ⊆ M.edgeSet
  have hpN : p N := ⟨hN, by simp⟩
  obtain ⟨M, _hNM, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpM, hmax'⟩
  refine ⟨M, hpM.2, hpM.1, ?_⟩
  intro K hMK hPK
  have hle : M ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hMK
  have hpK : p K := ⟨hPK, fun e he => hMK (hpM.2 he)⟩
  have hKM : K.edgeSet ⊆ M.edgeSet :=
    SimpleGraph.edgeSet_mono (hmax' hpK hle)
  exact le_antisymm hKM hMK
