-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:32.901553+00:00
-- url     : https://prove2.me/submissions/616cbf89-23c9-479c-ad2d-dc553c2fc3e1

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockChildren
end ThreeSum.LightBlockChildren
namespace ThreeSum.LightBlockCoefficients
end ThreeSum.LightBlockCoefficients
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceHashes
end ThreeSum.LightBlockSourceHashes
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightMaskHashes
end ThreeSum.LightMaskHashes
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightReportingBinomial
end ThreeSum.LightReportingBinomial
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceFlagArray
end ThreeSum.LightSourceFlagArray
namespace ThreeSum.LightSourceMaskFlags
end ThreeSum.LightSourceMaskFlags
namespace ThreeSum.LightSourcePreparation
end ThreeSum.LightSourcePreparation
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum.LightSourceTrim
end ThreeSum.LightSourceTrim
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalParameterBounds
end ThreeSum.LocalParameterBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
end ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial
end ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
end ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
end ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
end ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
end ThreeSum1960614.Machine.ThreeSum.LightSourceTrim
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
end ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
end ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients
open _root_.ThreeSum.LightBlockCoefficients


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

























theorem time_bound (J L : ℕ) : _root_.ThreeSum.LightBlockCoefficients.time J L ≤ 300*(J+1)*(L+1) := by
  unfold _root_.ThreeSum.LightBlockCoefficients.time _root_.ThreeSum.LightBlockCoefficients.roundTime _root_.ThreeSum.LightScaleArray.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightBlockCoefficients

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L : ℕ) : _root_.ThreeSum.LightMaskBits.time L ≤ 300*(L+1)^2 := by
  unfold _root_.ThreeSum.LightMaskBits.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes
open _root_.ThreeSum.LightMaskHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1000000









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n : ℕ) : _root_.ThreeSum.LightMaskHashes.time L n ≤ 300*(L+1)*(n+1) := by
  unfold _root_.ThreeSum.LightMaskHashes.time _root_.Light.powTableTime _root_.ThreeSum.LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual Pascal lookup for reporting child and terminal candidate counts -/

namespace ThreeSum.LightReportingBinomial
open _root_.ThreeSum.LightReportingBinomial


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000






variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



theorem time_bound (n : ℕ) : _root_.ThreeSum.LightReportingBinomial.time n≤1100*(n+1)^2 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildTime_bound n
  have hp : 1≤(n+1)^2 := by
    have hp0 : 0<(n+1)^2 := by positivity
    omega
  unfold _root_.ThreeSum.LightReportingBinomial.time
  nlinarith

end ThreeSum.LightReportingBinomial

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration
open _root_.ThreeSum.LightSubsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (L k : ℕ) :
    _root_.ThreeSum.LightSubsetEnumeration.time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (_root_.ThreeSum.SubsetAddress.enumerationWork_bound L k)







end ThreeSum.LightSubsetEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds
open _root_.ThreeSum.LocalParameterBounds


open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(514*h) := by
  calc
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h ≤ 2^(464*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ ≤ 2^(514*h) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)



theorem root_bound (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.rootCeiling (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h-1)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.threshold_bound h
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.pow_pos (514*h)
  unfold _root_.ThreeSum.LocalCoverBounds.rootCeiling
  omega

theorem prime_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 2^(514*h+2) := by
  have hp := (_root_.ThreeSum.LocalCoverBounds.selectedPrime_spec (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)).2.2
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.root_bound h
  change _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega





























end ThreeSum.LocalParameterBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes
open _root_.ThreeSum.LightBlockSourceHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (J L n : ℕ) :
    _root_.ThreeSum.LightBlockSourceHashes.time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.time_bound J L
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.time_bound (J*L) n
  unfold _root_.ThreeSum.LightBlockSourceHashes.time
  nlinarith

end ThreeSum.LightBlockSourceHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights
open _root_.ThreeSum.LightQueryWeights


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (W : ℕ) : _root_.ThreeSum.LightQueryWeights.time W ≤ 500*(W+1)^2 := by
  unfold _root_.ThreeSum.LightQueryWeights.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag
open _root_.ThreeSum.LightSourceRowFlag


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem time_bound (L U : ℕ) :
    _root_.ThreeSum.LightSourceRowFlag.time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold _root_.ThreeSum.LightSourceRowFlag.time _root_.ThreeSum.LightSourceRowScan.time _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum.LightSourceFlagTest.time
  nlinarith

end ThreeSum.LightSourceRowFlag

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration
open _root_.ThreeSum.LightQueryEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    _root_.ThreeSum.LightQueryEnumeration.time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.time_bound W
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound c t
  unfold _root_.ThreeSum.LightQueryEnumeration.time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim
open _root_.ThreeSum.LightSourceTrim


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (J L U : ℕ) :
    _root_.ThreeSum.LightSourceTrim.time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.time_bound L U
  unfold _root_.ThreeSum.LightSourceTrim.time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100

end ThreeSum.LightSourceTrim

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren
open _root_.ThreeSum.LightBlockChildren


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



















theorem time_bound {W c h : ℕ} (hc : c ≤ W) :
    _root_.ThreeSum.LightBlockChildren.time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold _root_.ThreeSum.LightBlockChildren.time _root_.ThreeSum.LightReportingAffine.time
  nlinarith

end ThreeSum.LightBlockChildren

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags
open _root_.ThreeSum.LightSourceMaskFlags


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (J L U : ℕ) :
    _root_.ThreeSum.LightSourceMaskFlags.time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.time_bound (J*L)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceTrim.time_bound J L U
  unfold _root_.ThreeSum.LightSourceMaskFlags.time
  omega

end ThreeSum.LightSourceMaskFlags

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum.LightReportingTerminalMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



theorem time_bound (h J k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time h J k≤1600*(J*(464*h)+1)^2*(2^((J-k)*(2*h))+1) := by
  have hc : (J-k)*(2*h)≤J*(464*h) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.time_bound (h := (J-k)*h) hc).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.choose_le_two_pow _ _) 1))

end ThreeSum.LightReportingTerminalMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray
open _root_.ThreeSum.LightSourceFlagArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceFlagProduct
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n J L U : ℕ) :
    _root_.ThreeSum.LightSourceFlagArray.time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceMaskFlags.time_bound J L U
  unfold _root_.ThreeSum.LightSourceFlagArray.time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10

end ThreeSum.LightSourceFlagArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation
open _root_.ThreeSum.LightSourcePreparation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n J L U : ℕ) :
    _root_.ThreeSum.LightSourcePreparation.time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.time_bound J L n
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagArray.time_bound n J L U
  unfold _root_.ThreeSum.LightSourcePreparation.time
  omega

end ThreeSum.LightSourcePreparation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




theorem size_bounds (h J : ℕ) :
    1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧ J+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧ 464*h+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      1026*h+4 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      J*(464*h)+(514*h+2)*(J+1)+2 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [_root_.ThreeSum.SharedTraversalCosts.size,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] <;> nlinarith

theorem log_local_le (h : ℕ) : Nat.log 2 (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1 ≤ 1026*h+4 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.prime_bound h
  have hw : 464*h ≤ 2^(464*h) := (Nat.lt_two_pow_self (n := 464*h)).le
  have hh : 464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 2^(1026*h+2) := by
    calc
      _ ≤ 2^(464*h)*2^(514*h+2) := Nat.mul_le_mul hw hp
      _ ≤ _ := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
  have hh' : 464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1 ≤ 2^(1026*h+3) := by
    have hz := Nat.two_pow_pos (1026*h+2)
    rw [show 1026*h+3=(1026*h+2)+1 by omega,pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) hh'
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem log_endpoint_le (h J : ℕ) :
    Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+1 ≤
      J*(464*h)+(514*h+2)*(J+1)+2 := by
  let W := J*(464*h)
  let E := W+(514*h+2)*(J+1)
  have hpow : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 2^((514*h+2)*(J+1)) := by
    rw [← pow_succ]
    exact (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.prime_bound h) _).trans_eq
      (pow_mul _ _ _).symm
  have hw : W ≤ 2^W := (Nat.lt_two_pow_self (n := W)).le
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J ≤ 2^E := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound
    change W*(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ 2^E
    exact (Nat.mul_le_mul hw hpow).trans_eq (pow_add 2 W ((514*h+2)*(J+1))).symm
  have he' : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1 ≤ 2^(E+1) := by
    have hz := Nat.two_pow_pos E
    rw [pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) he'
  rw [Nat.log_pow (by decide)] at hl
  dsimp [E,W] at hl
  omega

theorem residue_le_size (h J : ℕ) :
    _root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) ≤ 77*_root_.ThreeSum.SharedTraversalCosts.size h J := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds h J
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.log_endpoint_le h J
  unfold _root_.ThreeSum.LightResidues.residueBudget
  omega

theorem preparation_time_le (h J n : ℕ) :
    _root_.ThreeSum.LightSourcePreparation.time n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤
      4000*(_root_.ThreeSum.SharedTraversalCosts.size h J)^2*(n+1) := by
  let B := _root_.ThreeSum.SharedTraversalCosts.size h J
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds h J
  have hlog := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.log_local_le h).trans hb.2.2.2.2.1
  have hJ : J+1 ≤ B := hb.2.1
  have hL : 464*h+1 ≤ B := hb.2.2.1
  have hW : J*(464*h)+1 ≤ B := hb.2.2.2.1
  have hp : 1 ≤ B := hb.1
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hbase := Nat.mul_le_mul hJ hL
  have hrow : J*(150*(464*h)+464*(Nat.log 2 (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1)+250) ≤
      864*B^2 := by
    calc
      _ ≤ B*(864*B) := Nat.mul_le_mul (by omega : J ≤ B) (by omega)
      _ = _ := by ring
  have hmain : 300*(J*(464*h)+1)^2+
      J*(150*(464*h)+464*(Nat.log 2 (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+1)+250)+400 ≤ 1564*B^2 := by
    have hs := Nat.pow_le_pow_left hW 2
    nlinarith
  have htime := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourcePreparation.time_bound n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
  have hfirst : 300*(J+1)*(464*h+1) ≤ 300*B^2 := by nlinarith [hbase]
  have hsecond := Nat.mul_le_mul_right (n+1) (show 600*(J*(464*h)+1) ≤ 600*B^2 by omega)
  have hthird := Nat.mul_le_mul_left n hmain
  change _root_.ThreeSum.LightSourcePreparation.time n J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ 4000*B^2*(n+1)
  nlinarith











end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le__implementation_8f9508cefa (h J K : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge h J K+240 ≤
      31000*(_root_.ThreeSum.SharedTraversalCosts.size h J)^2*2^((J-K)*(2*h)) := by
  let B := _root_.ThreeSum.SharedTraversalCosts.size h J
  let T := 2^((J-K)*(2*h))
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds h J
  have hp : 1 ≤ B := hb.1
  have ht : 1 ≤ T := Nat.two_pow_pos _
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hc : _root_.ThreeSum.LightReportingTerminalMasks.count h J K ≤ T := Nat.choose_le_two_pow _ _
  have hr : (J-K)*(2*h)+1 ≤ B := by
    have hs := Nat.mul_le_mul (Nat.sub_le J K) (by omega : 2*h ≤ 464*h)
    have hw := hb.2.2.2.1
    change J*(464*h)+1 ≤ B at hw
    omega
  have hbin := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBinomial.time_bound ((J-K)*(2*h))).trans
    (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left hr 2))
  have hbinT := hbin.trans (Nat.le_mul_of_pos_right _ ht)
  have hmask := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time_bound h J K
  have hmaskT : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time h J K ≤ 3200*B^2*T := by
    calc
      _ ≤ 1600*B^2*(2*T) := hmask.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 1600 (Nat.pow_le_pow_left hb.2.2.2.1 2)) (by change T+1 ≤ 2*T; omega))
      _ = _ := by ring
  have hprep := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.preparation_time_le h J (_root_.ThreeSum.LightReportingTerminalMasks.count h J K)
  have hprepT : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time h J (_root_.ThreeSum.LightReportingTerminalMasks.count h J K) ≤
      16800*B^2*T := by
    have hm := hprep.trans (Nat.mul_le_mul_left (4000*B^2) (show
      _root_.ThreeSum.LightReportingTerminalMasks.count h J K+1 ≤ 2*T by omega))
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time
    nlinarith [Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht]
  have hres := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residue_le_size h J
  have hresT : (2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+1300)*T ≤
      1454*B^2*T := Nat.mul_le_mul_right T (by nlinarith)
  have hconstant : 2070 ≤ 2070*B^2*T := by
    have hh := Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht
    nlinarith
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge
  change _root_.ThreeSum.LightReportingBinomial.time ((J-K)*(2*h))+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time h J K+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalPreparation.time h J (_root_.ThreeSum.LightReportingTerminalMasks.count h J K)+
    (2*_root_.ThreeSum.LightResidues.residueBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J)+1300)*T+1830+240 ≤
      31000*B^2*T
  nlinarith only [hbinT,hmaskT,hprepT,hresT,hconstant]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le__implementation_8f9508cefa) := (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le__implementation_8f9508cefa)

#print axioms solution
