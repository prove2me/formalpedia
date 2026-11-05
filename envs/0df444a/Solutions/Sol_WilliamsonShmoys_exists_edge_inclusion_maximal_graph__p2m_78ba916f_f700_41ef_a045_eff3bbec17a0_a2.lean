-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:46:15.243359+00:00
-- url     : https://prove2.me/submissions/76005322-4dc2-4767-91e4-5313cbe8d1d6

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ P H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → P K → K.edgeSet = H.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ G.edgeSet ⊆ H.edgeSet
  have hpG : p G := ⟨hG, by simp⟩
  obtain ⟨H, _hGH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpH, hmax'⟩
  refine ⟨H, hpH.2, hpH.1, ?_⟩
  intro K hHK hPK
  have hle : H ≤ K := SimpleGraph.edgeSet_subset_edgeSet.mp hHK
  have hpK : p K := ⟨hPK, fun e he => hHK (hpH.2 he)⟩
  have hKH : K.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_mono (hmax' hpK hle)
  exact le_antisymm hKH hHK
