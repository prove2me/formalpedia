-- Prove2me | solution 1 for ThreeSum.Radix.radix_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:38.504162+00:00
-- url     : https://prove2.me/submissions/cd25fb1d-4939-44ae-95dd-c993f87d1ec4

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]


















/-- Divisibility through one radix digit. -/
theorem radix_divisibility_sourceProof (p a h t : ℤ) (hp : p ≠ 0) (j : ℕ) :
    p ^ (j + 1) ∣ a - (h + p * t) ↔
      p ∣ a - h ∧ p ^ j ∣ (a - h) / p - t := by
  constructor
  · intro hd
    have hd₁ : p ∣ a - h := by
      have hpow : p ∣ p ^ (j + 1) := dvd_pow_self _ (by omega)
      have hm : p ∣ p * t := dvd_mul_right _ _
      have hs := Int.dvd_add (dvd_trans hpow hd) hm
      convert hs using 1 <;> ring
    refine ⟨hd₁, ?_⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp] at hd
    exact hd
  · rintro ⟨hd₁, hd₂⟩
    have heq := Int.mul_ediv_cancel' hd₁
    have hrew : a - (h + p * t) = p * ((a - h) / p - t) := by
      nlinarith
    rw [hrew, pow_succ', mul_dvd_mul_iff_left hp]
    exact hd₂





































































end ThreeSum.Radix

end


theorem solution : ∀ (p a h t : Int),
  @Ne.{1} Int p (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
    ∀ (j : Nat),
      Iff
        (@Dvd.dvd.{0} Int Int.instDvd
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) h
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) p t))))
        (And (@Dvd.dvd.{0} Int Int.instDvd p (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a h))
          (@Dvd.dvd.{0} Int Int.instDvd
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
              (@HDiv.hDiv.{0, 0, 0} Int Int Int (@instHDiv.{0} Int Int.instDiv)
                (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a h) p)
              t))) := by
  exact @ThreeSum.Radix.radix_divisibility_sourceProof

#print axioms solution
