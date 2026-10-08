-- Prove2me | solution 1 for ThreeSumApsp.pref_step
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:29.690311+00:00
-- url     : https://prove2.me/submissions/21157680-f5a2-4da3-9744-5208f8e81821

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The prefixes of a binary representation, one bit at a time

The prefixes `⌊z/2^ℓ⌋` of a number `0 ≤ z < 2^L` are computed without division, from the level
`ℓ = L` down to `ℓ = 0`.  Next to the prefix `q = ⌊z/2^ℓ⌋` (`prefQ`) one keeps the rest of the
number, moved to the top: `r = (z mod 2^ℓ) 2^(L-ℓ) < 2^L` (`prefR`).  One step doubles `r`; if the
result reaches `2^L`, then the next bit of `z` is 1 (`pref_step`).  The bit is the binary digit
number `ℓ` of `z` (`testBit_iff_shift`).  One step on lists of numbers is `zipWith_shiftQ` and
`map_shiftR`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Prefixes, one bit at a time -/





















/-- **One step**: the prefix and the rest at the level `ℓ` are `shiftQ` and `shiftR` of those at the
level `ℓ + 1`. -/
theorem pref_step_sourceProof {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (z : ℤ) :
    prefQ ℓ z = shiftQ (2 ^ L) (prefQ (ℓ + 1) z) (prefR L (ℓ + 1) z) ∧
      prefR L ℓ z = shiftR (2 ^ L) (prefR L (ℓ + 1) z) := by
  -- In terms of `m = 2^ℓ` and `s = 2^(L - ℓ - 1)`.
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [prefQ, prefR, shiftQ, shiftR, Nat.add_sub_cancel_left,
    show ℓ + 1 + j - ℓ = j + 1 by omega]
  rw [show (2 : ℤ) ^ (ℓ + 1 + j) = 2 * 2 ^ ℓ * 2 ^ j by ring,
    show (2 : ℤ) ^ (ℓ + 1) = 2 * 2 ^ ℓ by ring, show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
  have hm : (0 : ℤ) < 2 ^ ℓ := by positivity
  have hs : (0 : ℤ) < 2 ^ j := by positivity
  generalize (2 : ℤ) ^ ℓ = m at hm
  generalize (2 : ℤ) ^ j = s at hs
  -- Write `z = 2 m a + b` with `0 ≤ b < 2 m`; the next bit of `z` is 0 exactly if `b < m`.
  have hz := Int.mul_ediv_add_emod z (2 * m)
  have hb0 := Int.emod_nonneg z (show 2 * m ≠ 0 by omega)
  have hb2 := Int.emod_lt_of_pos z (show 0 < 2 * m by omega)
  generalize z / (2 * m) = a at hz
  generalize z % (2 * m) = b at hz hb0 hb2
  by_cases hb : b < m
  · have hcond : 2 * (b * s) < 2 * m * s := by linarith [mul_pos (sub_pos.2 hb) hs]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a) (r := b)).2
      ⟨by linarith, hb0, hb⟩
    rw [if_pos hcond, if_pos hcond, hq, hr]
    exact ⟨rfl, by ring⟩
  · have hcond : ¬ 2 * (b * s) < 2 * m * s := by
      linarith [mul_nonneg (sub_nonneg.2 (not_lt.1 hb)) hs.le]
    obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique hm (a := z) (q := 2 * a + 1) (r := b - m)).2
      ⟨by linarith, by omega, by omega⟩
    rw [if_neg hcond, if_neg hcond, hq, hr]
    exact ⟨rfl, by ring⟩
































/-! ## The lists of the prefixes and of the rests -/




















end ThreeSumApsp

end


theorem solution : ∀ {L ℓ : Nat},
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      L →
    ∀ (z : Int),
      And
        (@Eq.{1} Int (ThreeSumApsp.prefQ ℓ z)
          (ThreeSumApsp.shiftQ
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) L)
            (ThreeSumApsp.prefQ
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z)
            (ThreeSumApsp.prefR L
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z)))
        (@Eq.{1} Int (ThreeSumApsp.prefR L ℓ z)
          (ThreeSumApsp.shiftR
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) L)
            (ThreeSumApsp.prefR L
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ℓ
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              z))) := by
  exact @ThreeSumApsp.pref_step_sourceProof

#print axioms solution
