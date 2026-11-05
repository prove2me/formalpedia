-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:42:41.481973+00:00
-- url     : https://prove2.me/submissions/e1efcf35-3081-4f40-a96b-be865932bba4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        P K →
        K.edgeSet ⊆ M.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun M => N.edgeSet ⊆ M.edgeSet ∧ P M
  have hpN : p N := ⟨(by intro x hx; exact hx), hN⟩
  obtain ⟨M, hNM, hMmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hMmax with ⟨hMp, hmax⟩
  have hNM' : N.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hNM
  refine ⟨M, hNM', hMp.2, ?_⟩
  intro K hMK hPK
  have hMK' : M ≤ K := (SimpleGraph.edgeSet_subset_edgeSet).mp hMK
  have hKM : K ≤ M := hmax ⟨hNM'.trans hMK, hPK⟩ hMK'
  exact SimpleGraph.edgeSet_mono hKM
