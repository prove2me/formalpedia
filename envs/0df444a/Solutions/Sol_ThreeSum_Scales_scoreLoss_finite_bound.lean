-- Prove2me | solution 1 for ThreeSum.Scales.scoreLoss_finite_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:59:48.755738+00:00
-- url     : https://prove2.me/submissions/e211db7b-343f-4fbd-a6f9-8ba05b2dc90f

import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

















































































noncomputable section




















































































































































































































































































































































































































































































































































































































/-- A finite algebraic transfer of the actual prime-chain contraction to
the explicit accumulated score loss. The two count inequalities are the
outputs of `PrimeChain.modulus_score_bound` and `modulus_bounds`. -/
theorem scoreLoss_finite_bound_sourceProof {k n H H₁ P : ℕ}
    (hC : 0 < (PrimeDensity.candidates (primeWindow n)).card)
    (hbudget : divisorBudget k n * primeWindow n ≤
      (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)))
    (hcontract : (PrimeDensity.candidates (primeWindow n)).card ^ primeDepth radix n * H ≤
      divisorBudget k n ^ primeDepth radix n * H₁)
    (hP : P ≤ (4 * primeWindow n) ^ primeDepth radix n) :
    P * H ≤ scoreLoss k n * H₁ := by
  let C := (PrimeDensity.candidates (primeWindow n)).card
  let r := primeDepth radix n
  let A := 4 * (k + 2) * (inputBits n + 1)
  have hpow := Nat.pow_le_pow_left hbudget r
  have hbig : C ^ r * (primeWindow n ^ r * H) ≤ C ^ r * (A ^ r * H₁) := by
    calc
      C ^ r * (primeWindow n ^ r * H) = primeWindow n ^ r * (C ^ r * H) := by ring
      _ ≤ primeWindow n ^ r * (divisorBudget k n ^ r * H₁) :=
        Nat.mul_le_mul_left _ hcontract
      _ = (divisorBudget k n * primeWindow n) ^ r * H₁ := by rw [mul_pow]; ring
      _ ≤ (C * A) ^ r * H₁ := Nat.mul_le_mul_right _ hpow
      _ = C ^ r * (A ^ r * H₁) := by rw [mul_pow]; ring
  have hsmall : primeWindow n ^ r * H ≤ A ^ r * H₁ :=
    Nat.le_of_mul_le_mul_left hbig (Nat.pow_pos hC)
  calc
    P * H ≤ (4 * primeWindow n) ^ r * H := Nat.mul_le_mul_right _ hP
    _ = 4 ^ r * (primeWindow n ^ r * H) := by rw [mul_pow]; ring
    _ ≤ 4 ^ r * (A ^ r * H₁) := Nat.mul_le_mul_left _ hsmall
    _ = scoreLoss k n * H₁ := by
      rw [← mul_assoc, ← mul_pow]
      have heq : 4 * A = 16 * (k + 2) * (inputBits n + 1) := by dsimp [A]; ring
      rw [heq]
      rfl





































































































































































































end

end ThreeSum.Scales

end


theorem solution : ∀ {k n H H₁ P : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n))) →
    @LE.le.{0} Nat instLENat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.Scales.divisorBudget k n)
          (ThreeSum.Scales.primeWindow n))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      @LE.le.{0} Nat instLENat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Finset.card.{0} Nat (ThreeSum.PrimeDensity.candidates (ThreeSum.Scales.primeWindow n)))
              (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
            H)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (ThreeSum.Scales.divisorBudget k n) (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
            H₁) →
        @LE.le.{0} Nat instLENat P
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (ThreeSum.Scales.primeWindow n))
              (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n)) →
          @LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) P H)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.Scales.scoreLoss k n) H₁) := by
  exact @ThreeSum.Scales.scoreLoss_finite_bound_sourceProof

#print axioms solution
