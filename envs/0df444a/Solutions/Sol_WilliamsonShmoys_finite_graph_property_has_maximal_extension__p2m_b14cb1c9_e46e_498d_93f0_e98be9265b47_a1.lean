-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:39.886489+00:00
-- url     : https://prove2.me/submissions/5ffcef92-53fb-4208-adbc-e5e52ca97cad

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hG : P G) : ∃ W : SimpleGraph V, G ≤ W ∧ P W ∧
      ∀ H : SimpleGraph V, W ≤ H → P H → H = W := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ P H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    refine ⟨G, ?_⟩
    change G ≤ G ∧ P G
    exact ⟨le_rfl, hG⟩
  obtain ⟨W, hWmem, hWmax⟩ := hSfinite.exists_maximal hSnonempty
  change G ≤ W ∧ P W at hWmem
  refine ⟨W, hWmem.1, hWmem.2, ?_⟩
  intro H hWH hPH
  have hHmem : H ∈ S := by
    change G ≤ H ∧ P H
    exact ⟨hWmem.1.trans hWH, hPH⟩
  have hHW : H ≤ W := hWmax hHmem hWH
  exact le_antisymm hHW hWH