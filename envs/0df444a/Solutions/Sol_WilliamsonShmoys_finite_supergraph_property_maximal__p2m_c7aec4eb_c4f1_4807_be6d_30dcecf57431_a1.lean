-- Prove2me | solution 1 for WilliamsonShmoys.finite_supergraph_property_maximal__p2m_c7aec4eb_c4f1_4807_be6d_30dcecf57431_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:40.131032+00:00
-- url     : https://prove2.me/submissions/68a43370-ea5b-4281-9e50-941dab629d1f

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P L) :
    ∃ H : SimpleGraph V, L.edgeSet ⊆ H.edgeSet ∧ P H ∧
      ∀ M : SimpleGraph V, H.edgeSet ⊆ M.edgeSet → P M → H = M := by
  classical
  let Q : SimpleGraph V → Prop := fun G => L.edgeSet ⊆ G.edgeSet ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := by
    exact ⟨L, by simp [Q, hP]⟩
  obtain ⟨H, instH, hmax⟩ := (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  letI := instH
  refine ⟨H, hmax.1.1, hmax.1.2, ?_⟩
  intro M hHM hPM
  have hQM : Q M := ⟨hmax.1.1.trans hHM, hPM⟩
  have hle : H ≤ M := (SimpleGraph.edgeSet_subset_edgeSet).1 hHM
  exact (SimpleGraph.IsExtremal.le_iff_eq hmax hQM).1 hle