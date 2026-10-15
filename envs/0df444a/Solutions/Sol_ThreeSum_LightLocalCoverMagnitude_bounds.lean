-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMagnitude.bounds
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:20:38.855842+00:00
-- url     : https://prove2.me/submissions/c6d21bbe-6d58-49d1-8c2a-d71ed78ef790

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
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
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_cap_bound
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_rounds_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
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

theorem prime_bound (h : ℕ) : localPrime h ≤ 2^(514*h+2) := by
  have hp := (selectedPrime_spec (localThreshold h)).2.2
  have hr := root_bound h
  change localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega

theorem width_bound (h : ℕ) : 512*h+1 ≤ 2^(h+10) := by
  have hh : h < 2^h := Nat.lt_two_pow_self
  have hp := pow_pos h
  rw [pow_add]
  norm_num
  omega


















































































































































end ThreeSum.LocalParameterBounds

end

section


/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude

open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout














theorem succ_pow_bound {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  have hp := Nat.two_pow_pos e
  rw [pow_succ]
  omega










































theorem bounds_sourceProof (h : ℕ) : Bounds h (magnitude h) := by
  have hs : 0 ≤ h*h := Nat.zero_le _
  have raise (e : ℕ) (he : e ≤ 600000*(h+1)^2) : 2^e ≤ magnitude h :=
    Nat.pow_le_pow_right (by decide) he
  have hp := LocalParameterBounds.prime_bound h
  have hN : rows h ≤ 2^((514*h+2)*(2*(512*h))) := by
    unfold rows
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  have hP : (localPrime h)^(2*(512*h)+1) ≤ 2^((514*h+2)*(2*(512*h)+1)) := by
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)+1) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  refine ⟨by exact Nat.two_pow_pos _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (LocalParameterBounds.width_bound h).trans (raise _ (by nlinarith only [hs]))
  · have hv : LightLocalCoverLayout.vertices h ≤ 2^(512*h) := Nat.choose_le_two_pow _ _
    exact (succ_pow_bound hv).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hp).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (cap_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hN).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (rounds_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hP).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (le_rfl : 2^(512*h+1) ≤ 2^(512*h+1))).trans
      (raise _ (by nlinarith only [hs]))

end ThreeSum.LightLocalCoverMagnitude

end


theorem solution : ∀ (h : Nat), ThreeSum.LightLocalCoverMagnitude.Bounds h (ThreeSum.LightLocalCoverMagnitude.magnitude h) := by
  exact @ThreeSum.LightLocalCoverMagnitude.bounds_sourceProof

#print axioms solution
