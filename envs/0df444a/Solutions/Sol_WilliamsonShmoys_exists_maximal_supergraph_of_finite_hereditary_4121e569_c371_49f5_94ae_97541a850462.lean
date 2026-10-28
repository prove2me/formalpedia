-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:35:05.581864+00:00
-- url     : https://prove2.me/submissions/27c7f968-ea66-4ceb-8ee4-bc59da9908ea

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ P H}
  have hS : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨H, hmax⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨H, hmax.1.1, hmax.1.2, ?_⟩
  intro K hHK hPK
  have hK : K ∈ S := ⟨hmax.1.1.trans hHK, hPK⟩
  exact le_antisymm (hmax.2 hK hHK) hHK