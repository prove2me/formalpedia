-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:33:14.495681+00:00
-- url     : https://prove2.me/submissions/d668bc5f-1c7d-42cf-88fd-d9f40ffd741e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        P N →
        N.edgeSet ⊆ M.edgeSet := by
  classical
  let Q : SimpleGraph V → Prop := fun M => K ≤ M ∧ P M
  have hQ : Q K := ⟨le_rfl, hK⟩
  obtain ⟨M, hKM, hmax⟩ := Finite.exists_le_maximal (p := Q) hQ
  have hQM : Q M := hmax.1
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.mpr hKM, hQM.2, ?_⟩
  intro N hMN hPN
  have hMleN : M ≤ N := SimpleGraph.edgeSet_subset_edgeSet.mp hMN
  by_contra hNsubM
  have hNleM : ¬ N ≤ M := fun h =>
    hNsubM (SimpleGraph.edgeSet_subset_edgeSet.mpr h)
  have hlt : M < N := by
    change M ≤ N ∧ ¬ N ≤ M
    exact ⟨hMleN, hNleM⟩
  have hQN : Q N := ⟨hKM.trans hMleN, hPN⟩
  exact hmax.not_prop_of_gt hlt hQN