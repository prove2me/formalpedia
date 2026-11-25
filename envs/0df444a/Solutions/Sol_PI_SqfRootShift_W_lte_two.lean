-- Prove2me | solution 1 for PI.SqfRootShift.W.lte_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:36.184861+00:00
-- url     : https://prove2.me/submissions/e695b908-f63e-45f7-aa34-45952a34c9be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    padicValNat 2 (g ^ k - 1) = padicValNat 2 (g - 1) + padicValNat 2 k := by
  have hgk : 2 ≤ g ^ k := le_trans hg (Nat.le_self_pow hk g)
  have hne1 : g ^ k - 1 ≠ 0 := by omega
  have hne2 : g - 1 ≠ 0 := by omega
  have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
    obtain ⟨t, ht⟩ := h4
    exact ⟨(t : ℤ), by omega⟩
  have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by
    have : ¬ 2 ∣ g := by omega
    exact_mod_cast this
  have key := Int.two_pow_sub_pow' k h4' hx
  rw [one_pow] at key
  have e1 : ((g : ℤ) ^ k - 1) = ((g ^ k - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g ^ k)]; ring
  have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
  have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
  rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity,
    Int.natCast_emultiplicity] at key
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hne1,
    padicValNat_eq_emultiplicity hne2, padicValNat_eq_emultiplicity hk]
  exact key
end PI.SqfRootShift.W
