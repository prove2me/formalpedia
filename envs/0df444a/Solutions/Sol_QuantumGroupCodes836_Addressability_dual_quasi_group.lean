-- Prove2me | solution 1 for QuantumGroupCodes836.Addressability.dual_quasi_group
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T14:59:47.974828+00:00
-- url     : https://prove2.me/submissions/3b4b4381-557a-46ab-92d7-60661417ed1b

import Definitions.Def_QuantumGroupCodes836_Addressability_Linear

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem dual_quasi_group {F G : Type} [Field F] [Fintype F] [Group G] [Fintype G]
    {n : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C) :
    ∃ B : CodeAction F (Fin n) G (dual C), B.coordinates = A.coordinates := by
  refine ⟨⟨A.coordinates, A.faithful, A.free, ?_⟩, rfl⟩
  intro g v hv c hc
  have h := hv (permute (A.coordinates g⁻¹) c) (A.preserves _ c hc)
  rw [← h]
  change ∑ i, v (A.coordinates g |>.symm i) * c i = ∑ i, v i * c (A.coordinates g⁻¹ |>.symm i)
  rw [← Equiv.sum_comp (A.coordinates g)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_inv]
  left
  rfl

end QuantumGroupCodes836.Addressability

open QuantumGroupCodes836.Addressability in
theorem solution {F G : Type} [Field F] [Fintype F] [Group G] [Fintype G]
    {n : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C) :
    ∃ B : CodeAction F (Fin n) G (dual C), B.coordinates = A.coordinates :=
  QuantumGroupCodes836.Addressability.dual_quasi_group C A
