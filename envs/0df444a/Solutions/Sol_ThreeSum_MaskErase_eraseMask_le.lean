-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:51:24.298515+00:00
-- url     : https://prove2.me/submissions/6be7447d-de33-4326-a644-1839e4064f5d

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress








theorem eraseMask_le_sourceProof {L a m : ℕ} (hm : m < 2^L) : eraseMask L a m ≤ m := by
  induction L generalizing m with
  | zero => simp [eraseMask]
  | succ L ih =>
    by_cases hlo : m < 2^L
    · simpa only [eraseMask, hlo, ite_true] using ih hlo
    · have hm' : m-2^L < 2^L := by rw [pow_succ] at hm; omega
      rw [eraseMask, if_neg hlo]
      split
      · exact Nat.sub_le _ _
      · have hh := ih hm'
        omega

































































end ThreeSum.MaskErase

end


theorem solution : ∀ {L a m : Nat},
  @LT.lt.{0} Nat instLTNat m
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L) →
    @LE.le.{0} Nat instLENat (ThreeSum.MaskErase.eraseMask L a m) m := by
  exact @ThreeSum.MaskErase.eraseMask_le_sourceProof

#print axioms solution
