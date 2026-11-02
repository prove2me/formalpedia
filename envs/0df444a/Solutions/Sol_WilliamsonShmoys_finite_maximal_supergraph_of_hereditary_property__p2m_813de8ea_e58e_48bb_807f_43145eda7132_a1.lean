-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:23.119196+00:00
-- url     : https://prove2.me/submissions/aa064200-261c-4d36-aaf0-bfd11eeeb89e

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G)
    (hclosed : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {K | G ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  have hGmem : G ∈ S := by
    simp [S, hG]
  have hSnonempty : S.Nonempty := ⟨G, hGmem⟩
  obtain ⟨H, hHmem, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := ⟨hHmem.1.trans hHK, hK⟩
  have hKH : K ≤ H := hHmax hKmem hHK
  exact le_antisymm hKH hHK