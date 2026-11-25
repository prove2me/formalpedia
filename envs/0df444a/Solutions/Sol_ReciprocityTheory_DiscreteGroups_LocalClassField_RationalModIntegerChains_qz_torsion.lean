-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains.qz_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:06.132525+00:00
-- url     : https://prove2.me/submissions/85f239bd-74a2-4cf8-bc8d-b67395f906b9

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
open ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains
open scoped Nat
variable {A : Type} [AddCommGroup A]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains
theorem _root_.solution (x : QZ) : ∃ k : ℕ, 0 < k ∧ k • x = 0 := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨q.num, by
    show (q.num : ℚ) = _
    rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.RationalModIntegerChains
