-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:38:36.174884+00:00
-- url     : https://prove2.me/submissions/f9232ce5-11a1-4838-8283-37b741ba97ac

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.Filter
open _root_.Real
open scoped _root_.Topology
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

section

/-- A finite algebraic transfer of the actual prime-chain contraction to
the explicit accumulated score loss. The two count inequalities are the
outputs of `PrimeChain.modulus_score_bound` and `modulus_bounds`. -/
theorem ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound__implementation_60437db861 {k n H H₁ P : ℕ}
    (hC : 0 < (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card)
    (hbudget : _root_.ThreeSum.Scales.divisorBudget k n * _root_.ThreeSum.Scales.primeWindow n ≤
      (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card * (4 * (k + 2) * (_root_.ThreeSum.Scales.inputBits n + 1)))
    (hcontract : (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * H ≤
      _root_.ThreeSum.Scales.divisorBudget k n ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * H₁)
    (hP : P ≤ (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    P * H ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H₁ := by
  let C := (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card
  let r := _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n
  let A := 4 * (k + 2) * (_root_.ThreeSum.Scales.inputBits n + 1)
  have hpow := Nat.pow_le_pow_left hbudget r
  have hbig : C ^ r * (_root_.ThreeSum.Scales.primeWindow n ^ r * H) ≤ C ^ r * (A ^ r * H₁) := by
    calc
      C ^ r * (_root_.ThreeSum.Scales.primeWindow n ^ r * H) = _root_.ThreeSum.Scales.primeWindow n ^ r * (C ^ r * H) := by ring
      _ ≤ _root_.ThreeSum.Scales.primeWindow n ^ r * (_root_.ThreeSum.Scales.divisorBudget k n ^ r * H₁) :=
        Nat.mul_le_mul_left _ hcontract
      _ = (_root_.ThreeSum.Scales.divisorBudget k n * _root_.ThreeSum.Scales.primeWindow n) ^ r * H₁ := by rw [mul_pow]; ring
      _ ≤ (C * A) ^ r * H₁ := Nat.mul_le_mul_right _ hpow
      _ = C ^ r * (A ^ r * H₁) := by rw [mul_pow]; ring
  have hsmall : _root_.ThreeSum.Scales.primeWindow n ^ r * H ≤ A ^ r * H₁ :=
    Nat.le_of_mul_le_mul_left hbig (Nat.pow_pos hC)
  calc
    P * H ≤ (4 * _root_.ThreeSum.Scales.primeWindow n) ^ r * H := Nat.mul_le_mul_right _ hP
    _ = 4 ^ r * (_root_.ThreeSum.Scales.primeWindow n ^ r * H) := by rw [mul_pow]; ring
    _ ≤ 4 ^ r * (A ^ r * H₁) := Nat.mul_le_mul_left _ hsmall
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H₁ := by
      rw [← mul_assoc, ← mul_pow]
      have heq : 4 * A = 16 * (k + 2) * (_root_.ThreeSum.Scales.inputBits n + 1) := by dsimp [A]; ring
      rw [heq]
      rfl
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound__implementation_60437db861) := (@ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound__implementation_60437db861)

#print axioms solution
