-- Prove2me | solution 1 for Subgroup.two_mul_card_le_card_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:21.055018+00:00
-- url     : https://prove2.me/submissions/bdfd5e88-7030-4697-8f7b-f4af1c2a9ca8

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas

set_option autoImplicit false
open Nat
namespace Subgroup
theorem _root_.solution {α : Type*} [Group α] {H K : Subgroup α}
    [Finite K] (h : H < K) : 2 * Nat.card H ≤ Nat.card K := by
  have hmul := Subgroup.relIndex_mul_relIndex ⊥ H K bot_le h.le
  rw [H.relIndex_bot_left, K.relIndex_bot_left, mul_comm] at hmul
  suffices 2 ≤ H.relIndex K from (mul_le_mul_right (Nat.card H) this).trans_eq hmul
  by_contra
  interval_cases hrel : H.relIndex K
  · exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ (by simpa using hmul.symm)
  · exact h.not_ge (Subgroup.relIndex_eq_one.mp hrel)
end Subgroup
