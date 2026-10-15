-- Prove2me | solution 1 for ThreeSum.Cover.trimmed_support_lower
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:11:38.910839+00:00
-- url     : https://prove2.me/submissions/96a38780-137c-42cb-845d-12f33660af61

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Cover_support_cauchy


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite cover bounds

Finite, exact lemmas for the second-moment argument, deterministic averaging,
and composition used in the proposed construction.  A hypothesis about a
particular local hash family is a mathematical obligation, not an asserted
implementation or running-time theorem.
-/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

























/-- The trimmed second-moment estimate, without division or probabilities.
If the first moment is at least lambda/2 and the second at most 5 lambda,
at least a lambda/20 fraction of the finite sample space is nonzero. -/
theorem trimmed_support_lower_sourceProof {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    lam * Fintype.card Ω ≤
      20 * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hL : 0 < lam * Fintype.card Ω := mul_pos hlam hN
  have hc : (0 : ℝ) ≤ (univ.filter fun ω => f ω ≠ 0).card := by positivity
  have hS : 0 ≤ ∑ ω, f ω := le_trans (by positivity) hfirst
  have hsq := support_cauchy f
  have hup := mul_le_mul_of_nonneg_left hsecond hc
  have hlo : (lam * Fintype.card Ω) ^ 2 ≤ 4 * (∑ ω, f ω) ^ 2 := by
    nlinarith
  nlinarith




















































end ThreeSum.Cover

end

universe u_1

theorem solution : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [Nonempty.{u_1 + 1} Ω] (f : Ω → Real) {lam : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lam →
    @LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) lam
            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst)))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (∑ ω : Ω, f ω) →
      @LE.le.{0} Real Real.instLE
          (∑ ω : Ω,
            @HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (f ω)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 5)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
              lam)
            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst))) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) lam
            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 20)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Finset.card.{u_1} Ω
                {ω : Ω |
                  @Ne.{1} Real (f ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))}))) := by
  exact @ThreeSum.Cover.trimmed_support_lower_sourceProof

#print axioms solution
