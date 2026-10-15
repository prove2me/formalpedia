-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.space_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:45:08.193402+00:00
-- url     : https://prove2.me/submissions/db262930-9c6a-4602-b42d-09c3efa42e20

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
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
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds

section


/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds

open LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : localThreshold h ≤ 2^(514*h) := by
  calc
    localThreshold h ≤ 2^(512*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(514*h) := by rw [← pow_add]; congr 1 <;> omega




theorem root_bound (h : ℕ) : rootCeiling (localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (localThreshold h-1)
  have ht := threshold_bound h
  have hp := pow_pos (514*h)
  unfold rootCeiling
  omega









theorem width_bound (h : ℕ) : 512*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := pow_pos h
  rw [pow_add]
  norm_num
  omega

































































































theorem space_bound_sourceProof (work h : ℕ) : LightLocalParameters.space work h ≤ work+envelope h := by
  have hw := width_bound h
  have hs : (512*h+1)^2 ≤ 2^(2*h+20) := by
    have hp := Nat.pow_le_pow_left hw 2
    simpa only [← pow_mul,show (h+10)*2 = 2*h+20 by omega] using hp
  have hw' : 512*h+1 ≤ 2^(2*h+20) := hw.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : LightLocalCounts.space work h ≤ work+base h := by
    have hsum : (512*h+1)^2+(512*h+1) ≤ 2^(2*h+21) := by
      have he : (2 : ℕ)^(2*h+21) = 2*2^(2*h+20) := by
        rw [show 2*h+21 = (2*h+20)+1 by omega,pow_succ]
        omega
      rw [he]
      omega
    have hb : 2^(2*h+21) ≤ base h := Nat.pow_le_pow_right (by decide) (by omega)
    unfold LightLocalCounts.space LightPascal.tableSize
    omega
  have hr := root_bound h
  have hx := pow_pos (514*h)
  have hl := Nat.log_le_self 2 (4*rootCeiling (localThreshold h)+1)
  have hp : LightSelectedPrime.space work (localThreshold h) ≤ work+base h := by
    have hp' : LightSelectedPrime.space work (localThreshold h) ≤ work+2^(514*h+5) := by
      unfold LightSelectedPrime.space LightPrimePool.space
      rw [pow_add]
      norm_num
      omega
    exact hp'.trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)
  unfold LightLocalParameters.space
  exact (max_le hc hp).trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)





















end ThreeSum.LocalParameterBounds

end


theorem solution : ∀ (work h : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.LightLocalParameters.space work h)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work (ThreeSum.LocalParameterBounds.envelope h)) := by
  exact @ThreeSum.LocalParameterBounds.space_bound_sourceProof

#print axioms solution
