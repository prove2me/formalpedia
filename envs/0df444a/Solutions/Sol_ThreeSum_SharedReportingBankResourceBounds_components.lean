-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.components
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:20:41.406463+00:00
-- url     : https://prove2.me/submissions/a0c2bfd2-d4f1-4b38-931d-8e4381b7f6b4

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_rounds_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

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




































































end ThreeSum.LightLocalCoverMagnitude

end

section


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}




theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))




theorem microHalf_le_self (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)

theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))

theorem totalSize_le_self (m : ℕ) : totalSize m ≤ m := by
  have h := totalSize_upper m
  omega






























































































































































end ThreeSum.LightScales

end

section


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000













theorem level_le {J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold LightSwitchDepth.depth at hk
  omega











































































































end ThreeSum.SharedReportingBankLevels

end

section


/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000






























theorem levels_le (J : ℕ) : levels J ≤ J+1 := by
  have hh := level_le (show LightSwitchDepth.depth J ≤ LightSwitchDepth.depth J from le_rfl)
  unfold levels
  omega























































































































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000




























theorem primitive_bounds (n : ℕ) :
    half n ≤ inputBits n ∧ blocks n ≤ 20*inputBits n ∧
    2*half n*blocks n ≤ inputBits n ∧
    width (half n) (blocks n) ≤ 256*inputBits n := by
  have hh := LightScales.microHalf_le_self (inputBits n)
  have hj := LightScales.blockCount_le (inputBits n)
  have ht := LightScales.totalSize_le_self (inputBits n)
  change blocks n*(2*half n) ≤ inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold width localWidth
  nlinarith

theorem linear_le_magnitude (n : ℕ) : 2048*(inputBits n+1) ≤ magnitude n := by
  have hh : inputBits n+1 ≤ 2^(inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem components_sourceProof (n : ℕ) : Components n := by
  obtain ⟨hh,hJ,ht,hW⟩ := primitive_bounds n
  have hlin := linear_le_magnitude n
  have hk := levels_le (blocks n)
  have hprod : half n*blocks n ≤ inputBits n := by nlinarith
  have raise (e : ℕ) (he : e ≤ 2048*(inputBits n+1)) : 2^e ≤ magnitude n :=
    Nat.pow_le_pow_right (by decide) he
  refine ⟨by exact Nat.two_pow_pos _,by omega,by omega,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,by omega,?_⟩
  · unfold prefixCount
    apply raise
    have he : 2*((blocks n+1)*(512*half n))=
        2*width (half n) (blocks n)+2*(512*half n) := by unfold width localWidth; ring
    rw [he]
    omega
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · have hs := LightLocalCoverMagnitude.rounds_bound (half n)
    calc
      _ ≤ (2^(1029*half n+16))^(blocks n) := Nat.pow_le_pow_left hs _
      _ = 2^((1029*half n+16)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · exact (LocalParameterBounds.prime_bound (half n)).trans (raise _ (by omega))
  · rw [← pow_succ]
    calc
      _ ≤ (2^(514*half n+2))^(blocks n+1) := Nat.pow_le_pow_left (LocalParameterBounds.prime_bound (half n)) _
      _ = 2^((514*half n+2)*(blocks n+1)) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · calc
      _ ≤ (2^(512*half n+1))^(blocks n) :=
        Nat.pow_le_pow_left (LightLocalCoverMagnitude.succ_pow_bound le_rfl) _
      _ = 2^((512*half n+1)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by
        have he : (512*half n+1)*blocks n=width (half n) (blocks n)+blocks n := by unfold width localWidth; ring
        rw [he]
        omega)
  · unfold LightSwitchDepth.word
    omega


































































































































































































end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ (n : Nat), ThreeSum.SharedReportingBankResourceBounds.Components n := by
  exact @ThreeSum.SharedReportingBankResourceBounds.components_sourceProof

#print axioms solution
