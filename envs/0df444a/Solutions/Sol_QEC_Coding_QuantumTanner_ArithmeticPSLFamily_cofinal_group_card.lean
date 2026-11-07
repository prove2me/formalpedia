-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.cofinal_group_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:21:12.22106+00:00
-- url     : https://prove2.me/submissions/0fb297a1-271d-4e93-87d4-d7d9314c493f

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveLinearSize_field_card_le_psl_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable (p : ℕ) [hPrime : Fact p.Prime]

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
theorem _root_.solution : ∀ N : ℕ, ∃ n, N ≤ Fintype.card (GroupAt p n) := by
  intro N
  refine ⟨N, ?_⟩
  rw [← Nat.card_eq_fintype_card]
  apply le_trans _ (ProjectiveLinearSize.field_card_le_psl_card (K := FieldAt p N))
  rw [GaloisField.card p (2 * (N + 2)) (by omega)]
  have := Nat.lt_pow_self hPrime.out.one_lt (n := 2 * (N + 2))
  omega
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
