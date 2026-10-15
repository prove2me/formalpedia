-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.host_time_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:48.609053+00:00
-- url     : https://prove2.me/submissions/8b72adbf-b069-47af-8d52-b87a07308f7d

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingCosts_time_le_boxes

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightDownsetSize
end ThreeSum.LightDownsetSize
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LightSharedReportingCounts
end ThreeSum.LightSharedReportingCounts
namespace ThreeSum.LightSmallDivide
end ThreeSum.LightSmallDivide
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetSetup
end ThreeSum.LightSubsetSetup
namespace ThreeSum.LightSwitchCosts
end ThreeSum.LightSwitchCosts
namespace ThreeSum.LightSwitchDepth
end ThreeSum.LightSwitchDepth
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankCosts
end ThreeSum.SharedReportingBankCosts
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
end ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
end ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth
end ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition








theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega























end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal
open _root_.ThreeSum.LightPascal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



















theorem buildTime_bound (L : ℕ) : _root_.ThreeSum.LightPascal.buildTime L ≤ 1000*(L+1)^2 := by
  unfold _root_.ThreeSum.LightPascal.buildTime _root_.ThreeSum.LightPascal.rowTime _root_.ThreeSum.LightArray.linearTime
  simp only [_root_.Light.fillTime]
  nlinarith

end ThreeSum.LightPascal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide
open _root_.ThreeSum.LightSmallDivide


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (a b : ℕ) : _root_.ThreeSum.LightSmallDivide.time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold _root_.ThreeSum.LightSmallDivide.time
  omega

end ThreeSum.LightSmallDivide

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology

















































theorem totalSize_upper (m : ℕ) : 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ 203889696 * m := by
  have h := Nat.div_mul_le_self (203889696 * m) (20000000000 * _root_.ThreeSum.Scales.microSize m)
  convert h using 1 <;> simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount] <;> ring



noncomputable section







































































































































end

end ThreeSum.Scales

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









theorem blockCount_le (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ 20*m := by
  by_cases hs : _root_.ThreeSum.Scales.microSize m=0
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,hs]
  · have hspos : 1 ≤ _root_.ThreeSum.Scales.microSize m := by omega
    have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*_root_.ThreeSum.Scales.microSize m := by
      calc
        _ = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hspos
    have hu := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize at hu
    omega

theorem totalSize_le_self (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ m := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
  omega























end ThreeSum.LightScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup
open _root_.ThreeSum.LightSubsetSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightSubsetSetup.time L ≤ 1200*(L+1)^2 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound L
  unfold _root_.ThreeSum.LightSubsetSetup.time _root_.Light.powTableTime _root_.ThreeSum.LightSubsetAddress.rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable integer quartic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch
open _root_.ThreeSum.Switch


open _root_.Set
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 0

























noncomputable section































theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega









end
end ThreeSum.Switch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger
open _root_.ThreeSum.CostLedger


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 400000



















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n < n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (b := n)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n - 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)]
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    omega

theorem microOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < _root_.ThreeSum.CostLedger.microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes n j :=
  Nat.choose_pos (by omega)

theorem prefixBoxes_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n j :=
  Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices_pos n j) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes_pos n j)

noncomputable section















end
end ThreeSum.CostLedger

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize
open _root_.ThreeSum.LightDownsetSize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem time_bound (L : ℕ) : _root_.ThreeSum.LightDownsetSize.time L ≤ 1400*(L+1)^2 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold _root_.ThreeSum.LightDownsetSize.time _root_.ThreeSum.LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual computation of the terminal reporting depth -/

namespace ThreeSum.LightSwitchDepth
open _root_.ThreeSum.LightSwitchDepth


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J d : ℕ}









theorem time_bound (J : ℕ) : _root_.ThreeSum.LightSwitchDepth.time J ≤ 260*J+90 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.time_bound (13*J) 20
  unfold _root_.ThreeSum.LightSwitchDepth.time
  omega

end ThreeSum.LightSwitchDepth

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing
open _root_.ThreeSum.BlockSourceSharing


open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds









theorem occurrence_card (h J : ℕ) : Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) = _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]





















end ThreeSum.BlockSourceSharing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compute the two local combinatorial counts from an actual Pascal table -/

namespace ThreeSum.LightSharedReportingCounts
open _root_.ThreeSum.LightSharedReportingCounts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 1700000
set_option maxRecDepth 9000








theorem time_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time h ≤ 1500*(464*h+1)^2 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound (464*h)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time
  nlinarith [Nat.one_le_pow' 2 (464*h)]

end ThreeSum.LightSharedReportingCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts
open _root_.ThreeSum.SharedReportingCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000



















theorem terminal_le_blocks (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition (n := n) (le_refl (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n))
  change 20*_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n ≤ 13*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n at hh
  omega











end ThreeSum.SharedReportingCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount]























end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts
open _root_.ThreeSum.LightSwitchCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.Filter
open scoped _root_.Topology






theorem residual_le_bits (n j : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j ≤ _root_.ThreeSum.Scales.inputBits n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum.Scales.muZero n :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ _root_.ThreeSum.Scales.inputBits n := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.totalSize_le_self (_root_.ThreeSum.Scales.inputBits n)

theorem time_le_budget (n j : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.timeBudget n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.residual_le_bits n j
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.time _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.timeBudget
  omega

theorem depth_time_le_budget (n : ℕ) :
    _root_.ThreeSum.LightSwitchDepth.time (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum.LightSwitchCosts.depthBudget n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchDepth.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hJ := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n)
  unfold _root_.ThreeSum.LightSwitchCosts.depthBudget
  omega







noncomputable section









end
end ThreeSum.LightSwitchCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts
open _root_.ThreeSum.SourceBandCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds



























theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : _root_.ThreeSum.BandPartition.size N (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,_root_.ThreeSum.BandPartition.size]
  · have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    have hb' : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn]
    omega





end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts
open _root_.ThreeSum.SharedReportingBankCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.Filter
open _root_.ThreeSum.SharedReportingCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
open scoped _root_.Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000







theorem residual_eq (n k : ℕ) :
    _root_.ThreeSum.SharedReportingBankLevels.residual (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := by
  unfold _root_.ThreeSum.SharedReportingBankLevels.residual _root_.ThreeSum.SharedReportingCosts.half _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize _root_.ThreeSum.Scales.muZero _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem cut_eq (n k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k=
      _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.residual_eq]
  rfl

theorem levels_eq (n : ℕ) : _root_.ThreeSum.SharedReportingBankHeader.levels (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n)=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n+1 := rfl

theorem round_time_le {n k : ℕ} (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k+8 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k := by
  have hV : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*(464*_root_.ThreeSum.SharedReportingCosts.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hdownset := (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.time_bound ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*(464*_root_.ThreeSum.SharedReportingCosts.half n))).trans
    (Nat.mul_le_mul_left 1400 (Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2))
  have hswitch := _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.time_le_budget n k
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.residual_eq] at hswitch
  have hcatalog := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time_le_boxes hk
  have hextra : _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.time (_root_.ThreeSum.SharedReportingBankLevels.residual (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k)+
      _root_.ThreeSum.LightDownsetSize.time ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*(464*_root_.ThreeSum.SharedReportingCosts.half n))+2808 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundExtra n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundExtra
    omega
  have hextraBoxes := Nat.le_mul_of_pos_right (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundExtra n) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_pos n k)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.time _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.time
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.cut_eq]
  change _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead n+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundExtra n)*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.time (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) ≤
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k at hcatalog
  rw [Nat.add_mul]
  omega

theorem all_prefix_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n := by
  have h0 : 0 ∈ Finset.range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n+1) := by simp
  have hh := Finset.single_le_sum (f := fun k => _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k) (fun k _ => Nat.zero_le _) h0
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_pos n 0).trans_le hh

theorem pair_time_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.time (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) (_root_.ThreeSum.SharedReportingBankHeader.levels (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n))+1000 ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundOverhead n+1600)*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n := by
  have hsum : (∑ k ∈ Finset.range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n+1),
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.roundTime (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) k+8)) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.round_time_le
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.terminal_le_blocks n)))
  have hconstant := Nat.le_mul_of_pos_right 1600 (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.all_prefix_pos n)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.time _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLevels.time
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.levels_eq,Nat.add_mul]
  omega

theorem total_le {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤
      3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hB
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total _root_.ThreeSum.SharedReportingBankRows.pairs
  rw [show _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n)=_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n from
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount n]
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hc
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by ring
    _ ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by nlinarith



noncomputable section















end
end ThreeSum.SharedReportingBankCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.Filter
open _root_.ThreeSum.SharedReportingCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
open scoped _root_.Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.host_time_le__implementation_ce1ba504e5 {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.time (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget n := by
  have hproduct := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.total_le hB hC) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.pair_time_le n)
  have hmain : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingPair.time (_root_.ThreeSum.SharedReportingCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) (_root_.ThreeSum.SharedReportingBankHeader.levels (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n))+1000) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundOverhead n+1600)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.boxCount n := by
    convert hproduct using 1 <;> unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.boxCount <;> ring
  have hdepth := _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.depth_time_le_budget n
  have hcounts := _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time_bound (_root_.ThreeSum.SharedReportingCosts.half n)
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time (_root_.ThreeSum.SharedReportingCosts.half n) ≤ 1500*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2 at hcounts
  change _root_.ThreeSum.LightSwitchDepth.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) ≤ _root_.ThreeSum.LightSwitchCosts.depthBudget n at hdepth
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.time _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.time
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.overhead _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.setup
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.host_time_le__implementation_ce1ba504e5) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.host_time_le__implementation_ce1ba504e5)

#print axioms solution
