-- Prove2me | solution 1 for ThreeSum.LightSelectedPrime.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:58:30.005983+00:00
-- url     : https://prove2.me/submissions/0184a914-fda4-4a49-a1bd-7ffbefd4234a

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

section


/-!
# Executing the deterministic square-root prime selection

The candidate pool is scanned by the verified primality program. Its first
entry is exactly the minimum used by `LocalCoverBounds.selectedPrime`.
The input threshold is positive; the routine has no primality oracle or
externally supplied list of candidates.
-/

namespace ThreeSum.LightSelectedPrime

open Light LocalCoverBounds LightResidues

set_option maxHeartbeats 1000000





























variable {lim : Limits} {P : Program} {d : ℕ}
































































theorem pool_time_bound (y : ℕ) : LightPrimePool.time y ≤ 5000*(y+1)^3 := by
  have hlog := Nat.log_le_self 2 (4*y+1)
  have hres : residueBudget (4*y)+70 ≤ 172*y+190 := by
    unfold residueBudget
    omega
  have hprim : LightPrimality.time (4*y) (4*y) ≤ 4*y*(172*y+190)+70 := by
    unfold LightPrimality.time
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.sub_le _ _) hres) _
  have hpool : LightPrimePool.time y ≤ 3*y*(4*y*(172*y+190)+170)+100 := by
    unfold LightPrimePool.time
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  exact hpool.trans (by nlinarith [Nat.zero_le (y^3),Nat.zero_le (y^2)])

theorem time_bound_sourceProof (N : ℕ) : time N ≤ 6000*(N+2)^3 := by
  have hy : rootCeiling N ≤ N+1 := by
    unfold rootCeiling
    have hh := Nat.sqrt_le_self (N-1)
    omega
  have hp := pool_time_bound (rootCeiling N)
  have hs := Nat.sqrt_le_self (N-1)
  have hpow := Nat.pow_le_pow_left (show rootCeiling N+1 ≤ N+2 by omega) 3
  have hp' : LightPrimePool.time (rootCeiling N) ≤ 5000*(N+2)^3 :=
    hp.trans (Nat.mul_le_mul_left _ hpow)
  have hlinear : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2)^3 := by
    have hl : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2) := by omega
    exact hl.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide : 3 ≠ 0) (N+2)))
  unfold time sqrtTime
  omega

end ThreeSum.LightSelectedPrime

end


theorem solution : ∀ (N : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.LightSelectedPrime.time N)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 6000) (instOfNatNat (nat_lit 6000)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @ThreeSum.LightSelectedPrime.time_bound_sourceProof

#print axioms solution
