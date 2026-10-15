-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_word_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:06:15.678974+00:00
-- url     : https://prove2.me/submissions/4214cbe9-adc1-4865-b0c9-20a136b9b341

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_prime_core_word_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le

namespace Filter
end Filter
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandRawAResources
end ThreeSum.LightBandRawAResources
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

























end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



theorem prefix_length_le (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).length ≤ i := by
  induction i with
  | zero => simp [_root_.ThreeSum.LightPrimePool.scanned]
  | succ i ih =>
      unfold _root_.ThreeSum.LightPrimePool.scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega













theorem size_le (y : ℕ) : _root_.ThreeSum.LightPrimePool.size y ≤ 3*y := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_length_le y (3*y)





































variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightPrimePool

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources
open _root_.ThreeSum.LightBandRawAResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000









theorem count_le (n g : ℕ) : _root_.ThreeSum.ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g) 2)







end ThreeSum.LightBandRawAResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000







theorem scale_bounds (n : ℕ) : 100 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ n+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.EncodedColorResources.localEnvelope n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.Scales.primeWindow n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale
  omega

theorem local_bounds (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.Bounds (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n) := by
  have hm : _root_.ThreeSum.LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum.EncodedColorResources.localEnvelope n := by
    unfold _root_.ThreeSum.LightLocalCoverMagnitude.magnitude _root_.ThreeSum.EncodedColorResources.localEnvelope _root_.ThreeSum.LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩



theorem powers (n : ℕ) : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(464*_root_.ThreeSum.EncodedColorResources.half n)+1 := by have hh := Nat.two_pow_pos (464*_root_.ThreeSum.EncodedColorResources.half n); omega
  exact (Nat.pow_le_pow_left htwo (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)).trans (H.radixPower.trans hm)















noncomputable section





end
end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hn : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.1; omega
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.count_le n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))





























end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact finite resources for constructing the dense-stop counter

The power-loop bound includes its actual `(base+1)^(J+1)` intermediate.
The modular scoring workspace remains affine in an arbitrary destination.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem dense_base_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := H.rounds
    change _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n at hh
    omega
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := H.cap
    change _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n at hh
    omega
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 :=
      Nat.mul_le_mul hs (Nat.pow_le_pow_left hc 2)
    _ = _ := by ring

theorem dense_representation_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_representation_cap_le n).trans
    (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.1 2)

theorem dense_power_le (n : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1)^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1) ≤
      2*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 := by
  have hS : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
    omega
  by_cases hz : _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)=0
  · rw [hz]
    simp only [zero_add,one_pow]
    have hh : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
    omega
  · have hb : _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1 ≤ 2*_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) := by omega
    have hrep : (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_representation_le n
    have htwo : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n :=
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.2
    calc
      _ ≤ (2*_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1) := Nat.pow_le_pow_left hb _
      _ = 2*(2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*(_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.base (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) := by
        rw [mul_pow,pow_succ,pow_succ]
        ring
      _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2*
          (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul htwo hrep) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_base_le n))
      _ = _ := by ring

theorem dense_cap_word_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 100*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n
  have hS : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
    omega
  have hj : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.1
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := H.rounds
    change _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n at hh
    omega
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    have hh := H.cap
    change _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n at hh
    omega
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_power_le n
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_base_le n
  have hcs := Nat.pow_le_pow_left hc 2
  have h1 : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 := Nat.one_le_pow _ _ hS
  have h16 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 :=
    Nat.le_self_pow (by decide) _
  have h26 : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  have h36 : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseCap.word
  omega

theorem dense_score_word_le (n U : ℕ) :
    _root_.ThreeSum.LightBandWeightedScore.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) U ≤
      5000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6+4*U := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_core_word_bound n U
  unfold _root_.ThreeSum.LightEncodedColorPrimeCore.word at hh
  exact (le_max_right _ _).trans ((le_max_right _ _).trans hh)

theorem dense_score_product_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*
      (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*
        (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)*(_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)^3)) ≤
      9*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8 := by
  have hs : _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n) ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_le _).trans
      (Nat.mul_le_mul_left 3 (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.2)
  have hg : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1
  calc
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2*((3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2)*
        ((3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3)) :=
      Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_representation_le n)
        (Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n) (Nat.mul_le_mul hs (Nat.pow_le_pow_left hg 3)))
    _ = _ := by ring














end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_word_le__implementation_447d8b30ef (n U : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseWord n U ≤ 10000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8+4*U := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n
  have hS : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by omega
  have hn := H.2.1
  have hp := H.2.2.2.2.1
  have hy := H.2.2.2.2.2
  have hg := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1
  have hj : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.1
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_le (_root_.ThreeSum.Scales.primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_cap_word_le n
  have hscore := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_score_word_le n U
  have hprod := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_score_product_le n
  have hrep := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_representation_le n
  have h1 : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8 := Nat.one_le_pow _ _ hS
  have h18 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8 :=
    Nat.le_self_pow (by decide) _
  have h28 : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  have h68 : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^8 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseWord _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.word
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_word_le__implementation_447d8b30ef) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.dense_word_le__implementation_447d8b30ef)

#print axioms solution
