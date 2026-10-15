-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.dense_word_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:17:40.872551+00:00
-- url     : https://prove2.me/submissions/470e0b5f-5d04-44d2-9fee-a61b4b89e546

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_EncodedColorResources_prime_core_word_bound
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000






theorem prefix_length_le (y i : ℕ) : (scanned y i).length ≤ i := by
  induction i with
  | zero => simp [scanned]
  | succ i ih =>
      unfold scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega















































theorem size_le (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)







































































































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000






















theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)






















end ThreeSum.LightBandRawAResources

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)
























































noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section


/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : ColorBandBounds.count n (bandSize n) ≤ 3*(scale n)^2 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  exact (LightBandRawAResources.count_le n (bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))


































































































































































end ThreeSum.EncodedColorResources

end

section


/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales ArithmeticStageBounds GlobalEncoding LocalCoverBounds
open KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem dense_base_le (n : ℕ) :
    LightDenseCap.base (half n) ≤ (EncodedColorResources.scale n)^3 := by
  have H := EncodedColorResources.local_bounds n
  have hs : scheduleSize (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.rounds
    change scheduleSize (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hc : localBucketCap (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.cap
    change localBucketCap (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  calc
    _ ≤ EncodedColorResources.scale n*(EncodedColorResources.scale n)^2 :=
      Nat.mul_le_mul hs (Nat.pow_le_pow_left hc 2)
    _ = _ := by ring

theorem dense_representation_le (n : ℕ) :
    representationCap (half n) (blocks n) ≤ (EncodedColorResources.scale n)^2 :=
  (wanted_representation_cap_le n).trans
    (Nat.pow_le_pow_left (EncodedColorResources.scale_bounds n).2.2.1 2)

theorem dense_power_le (n : ℕ) :
    (LightDenseCap.base (half n)+1)^(blocks n+1) ≤
      2*(EncodedColorResources.scale n)^6 := by
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  by_cases hz : LightDenseCap.base (half n)=0
  · rw [hz]
    simp only [zero_add,one_pow]
    have hh : 1 ≤ (EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
    omega
  · have hb : LightDenseCap.base (half n)+1 ≤ 2*LightDenseCap.base (half n) := by omega
    have hrep : (LightDenseCap.base (half n))^(blocks n) ≤
        (EncodedColorResources.scale n)^2 := dense_representation_le n
    have htwo : 2^(blocks n) ≤ EncodedColorResources.scale n :=
      (EncodedColorResources.powers n).2.2.2
    calc
      _ ≤ (2*LightDenseCap.base (half n))^(blocks n+1) := Nat.pow_le_pow_left hb _
      _ = 2*(2^(blocks n)*(LightDenseCap.base (half n))^(blocks n)*LightDenseCap.base (half n)) := by
        rw [mul_pow,pow_succ,pow_succ]
        ring
      _ ≤ 2*(EncodedColorResources.scale n*(EncodedColorResources.scale n)^2*
          (EncodedColorResources.scale n)^3) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul htwo hrep) (dense_base_le n))
      _ = _ := by ring

theorem dense_cap_word_le (n : ℕ) :
    LightDenseCap.word (half n) (blocks n) ≤ 100*(EncodedColorResources.scale n)^6 := by
  have H := EncodedColorResources.local_bounds n
  have hS : 1 ≤ EncodedColorResources.scale n := by
    have hh := (EncodedColorResources.scale_bounds n).1
    omega
  have hj : blocks n+1 ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.1
  have hs : scheduleSize (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.rounds
    change scheduleSize (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hc : localBucketCap (half n) ≤ EncodedColorResources.scale n := by
    have hh := H.cap
    change localBucketCap (half n)+1 ≤ EncodedColorResources.scale n at hh
    omega
  have hp := dense_power_le n
  have hb := dense_base_le n
  have hcs := Nat.pow_le_pow_left hc 2
  have h1 : 1 ≤ (EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
  have h16 : EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^6 :=
    Nat.le_self_pow (by decide) _
  have h26 : (EncodedColorResources.scale n)^2 ≤ (EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  have h36 : (EncodedColorResources.scale n)^3 ≤ (EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold LightDenseCap.word
  omega

theorem dense_score_word_le (n U : ℕ) :
    LightBandWeightedScore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U ≤
      5000*(EncodedColorResources.scale n)^6+4*U := by
  have hh := EncodedColorResources.prime_core_word_bound n U
  unfold LightEncodedColorPrimeCore.word at hh
  exact (le_max_right _ _).trans ((le_max_right _ _).trans hh)

theorem dense_score_product_le (n : ℕ) :
    representationCap (half n) (blocks n)*
      (ColorBandBounds.count n (bandSize n)*
        (LightPrimePool.size (primeWindow n)*(bandSize n)^3)) ≤
      9*(EncodedColorResources.scale n)^8 := by
  have hs : LightPrimePool.size (primeWindow n) ≤ 3*EncodedColorResources.scale n :=
    (LightPrimePool.size_le _).trans
      (Nat.mul_le_mul_left 3 (EncodedColorResources.scale_bounds n).2.2.2.2.2)
  have hg : bandSize n ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.2.2.1
  calc
    _ ≤ (EncodedColorResources.scale n)^2*((3*(EncodedColorResources.scale n)^2)*
        ((3*EncodedColorResources.scale n)*(EncodedColorResources.scale n)^3)) :=
      Nat.mul_le_mul (dense_representation_le n)
        (Nat.mul_le_mul (EncodedColorResources.count_le n) (Nat.mul_le_mul hs (Nat.pow_le_pow_left hg 3)))
    _ = _ := by ring











theorem dense_word_le_sourceProof (n U : ℕ) : denseWord n U ≤ 10000*(EncodedColorResources.scale n)^8+4*U := by
  have H := EncodedColorResources.scale_bounds n
  have hS : 1 ≤ EncodedColorResources.scale n := by omega
  have hn := H.2.1
  have hp := H.2.2.2.2.1
  have hy := H.2.2.2.2.2
  have hg := (EncodedColorResources.dimensions n).2.2.2.1
  have hj : blocks n+1 ≤ EncodedColorResources.scale n := (EncodedColorResources.dimensions n).2.1
  have hr := EncodedColorResources.count_le n
  have hs := (LightPrimePool.size_le (primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := dense_cap_word_le n
  have hscore := dense_score_word_le n U
  have hprod := dense_score_product_le n
  have hrep := dense_representation_le n
  have h1 : 1 ≤ (EncodedColorResources.scale n)^8 := Nat.one_le_pow _ _ hS
  have h18 : EncodedColorResources.scale n ≤ (EncodedColorResources.scale n)^8 :=
    Nat.le_self_pow (by decide) _
  have h28 : (EncodedColorResources.scale n)^2 ≤ (EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  have h68 : (EncodedColorResources.scale n)^6 ≤ (EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold denseWord LightDenseSetup.word
  omega






















end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ (n U : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankResourceBounds.denseWord n U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.EncodedColorResources.scale n) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) U)) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.dense_word_le_sourceProof

#print axioms solution
