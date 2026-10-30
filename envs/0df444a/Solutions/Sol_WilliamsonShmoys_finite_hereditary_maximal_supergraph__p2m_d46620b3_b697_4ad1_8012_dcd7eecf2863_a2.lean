-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:46.905089+00:00
-- url     : https://prove2.me/submissions/1baf63c9-ed10-40af-a11b-73c8a28d8d50

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hP : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ G : SimpleGraph V, H ≤ G → P G → G ≤ H := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ P G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hH, hmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro G hHG hPG
  exact hmax ⟨hH.1.trans hHG, hPG⟩ hHG