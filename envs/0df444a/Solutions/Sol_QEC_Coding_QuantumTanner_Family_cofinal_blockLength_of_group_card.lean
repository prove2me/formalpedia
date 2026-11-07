-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Family.cofinal_blockLength_of_group_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:18:57.915051+00:00
-- url     : https://prove2.me/submissions/95d0799e-eefc-4110-9a34-b18b4b4950dc

import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_card_group_mul_local_degree_eq_twice_card_square


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe u v
open QEC.Coding.QuantumTanner.Family
namespace QEC.Coding.QuantumTanner.Family
theorem _root_.solution
    {Index : Type u} {G A B Square XBasis ZBasis : Index → Type v}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (Square i)]
    [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (Delta : Nat) (hDelta : 0 < Delta)
    (hA : ∀ i, Fintype.card (A i) = Delta)
    (hB : ∀ i, Fintype.card (B i) = Delta)
    (hGroups : ∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) :
    ∀ N : Nat, ∃ i, N ≤ (family i).blockLength := by
  intro N
  obtain ⟨i, hi⟩ := hGroups (2 * N)
  have hCard := (family i).complex.card_group_mul_local_degree_eq_twice_card_square
  rw [hA i, hB i, ← Nat.mul_assoc] at hCard
  have hFirst : Fintype.card (G i) ≤ Fintype.card (G i) * Delta :=
    Nat.le_mul_of_pos_right _ hDelta
  have hSecond : Fintype.card (G i) * Delta ≤ Fintype.card (G i) * Delta * Delta :=
    Nat.le_mul_of_pos_right _ hDelta
  refine ⟨i, ?_⟩
  change N ≤ Fintype.card (Square i)
  omega
end QEC.Coding.QuantumTanner.Family
