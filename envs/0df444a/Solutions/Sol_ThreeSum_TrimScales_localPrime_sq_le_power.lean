-- Prove2me | solution 1 for ThreeSum.TrimScales.localPrime_sq_le_power
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:53.927696+00:00
-- url     : https://prove2.me/submissions/0189453f-67eb-450d-8e38-06b052bcbf23

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Scales
end ThreeSum.Scales

section


/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology






















noncomputable section

































































































































theorem localPrime_sq_le_power_sourceProof (h : ℕ) :
    LocalCoverBounds.localPrime h ^ 2 ≤ 2 ^ (4 + 514 * h) := by
  have hM : LocalCoverBounds.outputCount (512 * h) h ≤ 2 ^ (512 * h) :=
    Nat.choose_le_two_pow _ _
  calc
    LocalCoverBounds.localPrime h ^ 2 ≤
        16 * (LocalCoverBounds.outputCount (512 * h) h * 2 ^ (2 * h)) :=
      LocalCoverBounds.localPrime_sq_upper h
    _ ≤ 16 * (2 ^ (512 * h) * 2 ^ (2 * h)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hM)
    _ = 2 ^ (4 + 514 * h) := by
      rw [← pow_add, show 512 * h + 2 * h = 514 * h by omega, pow_add]
      norm_num




















































































































































end

end ThreeSum.TrimScales

end


theorem solution : ∀ (h : Nat),
  @LE.le.{0} Nat instLENat
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (ThreeSum.LocalCoverBounds.localPrime h) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))) h))) := by
  exact @ThreeSum.TrimScales.localPrime_sq_le_power_sourceProof

#print axioms solution
