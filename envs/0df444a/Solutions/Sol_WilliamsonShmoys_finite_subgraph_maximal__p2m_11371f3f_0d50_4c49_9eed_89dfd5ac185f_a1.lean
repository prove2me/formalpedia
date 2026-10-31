-- Prove2me | solution 1 for WilliamsonShmoys.finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:07.683811+00:00
-- url     : https://prove2.me/submissions/b475688c-1ee0-4a58-ad56-95859d5dbd3b

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (P : SimpleGraph V → Prop) (hZ : P Z) (hdown : ∀ {G H : SimpleGraph V}, (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) → P H → P G) : ∃ H : SimpleGraph V, (∀ ⦃u v : V⦄, Z.Adj u v → H.Adj u v) ∧ Z.edgeSet.ncard ≤ H.edgeSet.ncard ∧ P H ∧ ∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → P K → K = H := by
  classical
  let Q : SimpleGraph V → Prop := fun G => Z ≤ G ∧ P G
  obtain ⟨H, dH, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨Z, le_rfl, hZ⟩
  refine ⟨H, ?_, ?_, hH.prop.2, ?_⟩
  · exact hH.prop.1
  · apply Set.ncard_mono
    exact edgeSet_subset_edgeSet.mpr hH.prop.1
  · intro K hHK hK
    exact ((SimpleGraph.IsExtremal.le_iff_eq hH ⟨hH.prop.1.trans hHK, hK⟩).mp hHK).symm