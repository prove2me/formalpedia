-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:28.617005+00:00
-- url     : https://prove2.me/submissions/b7066910-eb06-4b8d-b984-94a64dbbfdd7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      P H ∧
      (∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        P J →
        J.edgeSet ⊆ H.edgeSet) := by
  classical
  let S : Set (SimpleGraph V) := {G | K.edgeSet ⊆ G.edgeSet ∧ P G}
  have hS : S.Nonempty := ⟨K, ⟨Set.Subset.rfl, hK⟩⟩
  obtain ⟨H, hH, hmax⟩ :=
    finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2 S hS
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro J hHJ hPJ
  have hSJ : J ∈ S := ⟨hH.1.trans hHJ, hPJ⟩
  have hle : H ≤ J := (SimpleGraph.edgeSet_subset_edgeSet).1 hHJ
  exact (SimpleGraph.edgeSet_subset_edgeSet).2 (hmax J hSJ hle)