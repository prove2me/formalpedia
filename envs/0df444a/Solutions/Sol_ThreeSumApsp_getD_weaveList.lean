-- Prove2me | solution 1 for ThreeSumApsp.getD_weaveList
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:00.170219+00:00
-- url     : https://prove2.me/submissions/71465187-8aa7-460d-8498-78a55b495121

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Count
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Interleaving two strings of digits along a mask

A mask is a list of truth values, one for each level.  `weaveList mask outer inner` runs through the
levels and takes the next digit of `inner` at a level with the entry `true` and the next digit of
`outer` at a level with the entry `false`.  A program that forms the number with these digits by
Horner's rule needs one pass over the mask and two pointers: at level `ℓ` the pointer into `inner`
has passed as many digits as there are entries `true` among the first `ℓ` entries of the mask, and
the pointer into `outer` as many as there are entries `false` (`getD_weaveList`).
-/

@[expose] public section

namespace ThreeSumApsp









/-- `weaveList` has one digit for each level. -/
@[simp] theorem length_weaveList (mask : List Bool) (outer inner : List ℕ) :
    (weaveList mask outer inner).length = mask.length := by
  induction mask generalizing outer inner with
  | nil => simp [weaveList]
  | cons x mask ih => cases x <;> simp [weaveList, ih]

/-- The digit of `weaveList` at level `ℓ`: the next unused digit of `inner` or of `outer`. -/
theorem getD_weaveList_sourceProof (mask : List Bool) (outer inner : List ℕ) (ℓ : ℕ) :
    (weaveList mask outer inner).getD ℓ 0 =
      if ℓ < mask.length then
        if mask.getD ℓ false then inner.getD ((mask.take ℓ).count true) 0
        else outer.getD ((mask.take ℓ).count false) 0
      else 0 := by
  induction mask generalizing outer inner ℓ with
  | nil => simp [weaveList]
  | cons x mask ih =>
    cases ℓ with
    | zero =>
      cases x
      · cases outer <;> simp [weaveList]
      · cases inner <;> simp [weaveList]
    | succ ℓ =>
      cases x
      · cases outer with
        | nil => simpa [weaveList] using ih [] inner ℓ
        | cons o outer => simpa [weaveList] using ih outer inner ℓ
      · cases inner with
        | nil => simpa [weaveList] using ih outer [] ℓ
        | cons i inner => simpa [weaveList] using ih outer inner ℓ













end ThreeSumApsp

end


theorem solution : ∀ (mask : List.{0} Bool) (outer inner : List.{0} Nat) (ℓ : Nat),
  @Eq.{1} Nat
    (@List.getD.{0} Nat (ThreeSumApsp.weaveList mask outer inner) ℓ
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat ℓ (@List.length.{0} Bool mask)) (ℓ.decLt (@List.length.{0} Bool mask))
      (@ite.{1} Nat (@Eq.{1} Bool (@List.getD.{0} Bool mask ℓ Bool.false) Bool.true)
        (instDecidableEqBool (@List.getD.{0} Bool mask ℓ Bool.false) Bool.true)
        (@List.getD.{0} Nat inner
          (@List.count.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) Bool.true
            (@List.take.{0} Bool ℓ mask))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.getD.{0} Nat outer
          (@List.count.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) Bool.false
            (@List.take.{0} Bool ℓ mask))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  exact @ThreeSumApsp.getD_weaveList_sourceProof

#print axioms solution
