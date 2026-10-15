-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:07:04.405014+00:00
-- url     : https://prove2.me/submissions/61cde060-8160-4009-85af-05d98240d716

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

local instance platformRadixNonzero_43ce750337 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


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
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
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
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
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
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales
open _root_.ThreeSum.LightScales


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem inputBits_le_self (n : ℕ) : _root_.ThreeSum.Scales.inputBits n ≤ n := by
  simpa [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using Nat.log_le_self 2 n

































end ThreeSum.LightScales

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



theorem word_le (W n g U : ℕ) :
    _root_.ThreeSum.LightBandRawAColor.word W n g U ≤ 2^(W+1)+3*n^2+29*n+2*g+9*U+100 := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g
  have hq := Nat.pow_le_pow_left hm 2
  unfold _root_.ThreeSum.LightBandRawAColor.word _root_.ThreeSum.LightColorBands.word _root_.ThreeSum.ColorBandBounds.word
    _root_.ThreeSum.LightBandEnumeration.word _root_.ThreeSum.LightBandRawACatalog.word _root_.ThreeSum.LightBandCandidates.word
    _root_.ThreeSum.LightBandRawA.word _root_.ThreeSum.LightBandEnumeration.count
  nlinarith only [hm,hq]



end ThreeSum.LightBandRawAResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Proved polynomial limits for original-input band and incidence preprocessing -/

namespace ThreeSum.LightBandRawAResources
open _root_.ThreeSum.LightBandRawAResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000








theorem color_power_le (n : ℕ) : 2^((_root_.ThreeSum.Scales.inputBits n+1)+1) ≤ 4*(n+1) := by
  have hp : 2^(_root_.ThreeSum.Scales.inputBits n) ≤ n+1 := by
    simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using Nat.pow_log_le_add_one 2 n
  calc
    _ = 4*2^(_root_.ThreeSum.Scales.inputBits n) := by
      rw [show _root_.ThreeSum.Scales.inputBits n+1+1=_root_.ThreeSum.Scales.inputBits n+2 by omega,pow_add]
      norm_num
      ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hp







noncomputable section







end
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















theorem normalized_word_bound (n U : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.word n U ≤ 400*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2+9*U := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hn := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.1
  have hg := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1
  have hW := (Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.inputBits_le_self n) 1).trans hn
  have hpow := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.color_power_le n).trans (Nat.mul_le_mul_left 4 hn)
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n
  have hn2 := Nat.pow_le_pow_left (show n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n by omega) 2
  have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.word_le (_root_.ThreeSum.Scales.inputBits n+1) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) U
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.word _root_.ThreeSum.LightEncodedColorLayout.word
  nlinarith only [hb,hn,hg,hW,hpow,hcount,hn2,hraw]













end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources

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
section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_word_bound__implementation_1c5dd23e46 (n U : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputWord n U ≤ 10000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6+9*U := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hn := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.1
  have hg := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1
  have hM := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  have hy := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.2
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n
  have hnrm := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.normalized_word_bound n U
  have hcore := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_core_word_bound n U
  have hp16 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hcountEq : _root_.ThreeSum.LightEncodedColorPrime.count n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)=_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
    unfold _root_.ThreeSum.LightEncodedColorPrime.count _root_.ThreeSum.ColorBandBounds.count
    ring
  have hprime : _root_.ThreeSum.LightEncodedColorPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) U ≤
      6000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6+4*U := by
    unfold _root_.ThreeSum.LightEncodedColorPrime.word
    rw [hcountEq]
    nlinarith only [hb,hn,hR,hcore,hp16,hp26]
  have hmax : max (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.word n U)
      (_root_.ThreeSum.LightEncodedColorPrime.word (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) U) ≤
      9000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^6+9*U := max_le (by nlinarith only [hnrm,hp26]) (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputWord
  nlinarith only [hb,hg,hM,hy,hmax,hp16]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_word_bound__implementation_1c5dd23e46) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.prime_word_bound__implementation_1c5dd23e46)

#print axioms solution
