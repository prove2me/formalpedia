-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.wanted_source_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:50:37.364972+00:00
-- url     : https://prove2.me/submissions/8b34d13f-30b4-4da4-ab75-9984f5c21137

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_global_keys_space_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverResources_space_polynomial
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalParameterBounds_space_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components

local instance platformRadixNonzero_1d4c54501b (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.EncodedColorWantedCosts
end ThreeSum.EncodedColorWantedCosts
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandRawAResources
end ThreeSum.LightBandRawAResources
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightLocalCoverInitResources
end ThreeSum.LightLocalCoverInitResources
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverResources
end ThreeSum.LightLocalCoverResources
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
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
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

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

/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables



















theorem schedule_end_le_space (base h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h := Nat.le_max_right ..



end ThreeSum.LightLocalCoverLayout

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

/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources
open _root_.ThreeSum.LightLocalCoverResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude

set_option maxHeartbeats 1800000













theorem space_bound (base h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h ≤ base+_root_.ThreeSum.LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.space_polynomial (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds h) base).trans
  apply Nat.add_le_add_left
  calc
    20*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^3 ≤ 2^5*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+600000*(h+1)^2*3) := by rw [_root_.ThreeSum.LightLocalCoverMagnitude.magnitude,← pow_mul,← pow_add]
    _ ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)
















end ThreeSum.LightLocalCoverResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000













theorem nextFree_le_space (base h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.schedule_end_le_space base h

end ThreeSum.LightLocalCoverRetention

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData
open _root_.ThreeSum.LightCoverKeyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000











theorem keyEnd_le_space (free h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space free h J := by
  have hg : _root_.ThreeSum.LightRadixKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h) h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h) h J :=
    le_max_right _ _
  exact hg.trans (le_max_right _ _)







end ThreeSum.LightCoverKeyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources
open _root_.ThreeSum.LightLocalCoverInitResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    _root_.ThreeSum.LocalParameterBounds.envelope h ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]

theorem constant_le (h : ℕ) : 600 ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  exact (by decide : 600 ≤ 2^10).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem four_envelope_le (h : ℕ) :
    4*_root_.ThreeSum.LightLocalCoverResources.envelope h ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)







theorem space_bound (free h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space free h ≤ free+_root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.space_bound (_root_.ThreeSum.LightLocalCoverInit.base free) h).trans
    (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.parameters_envelope_le h) (_root_.ThreeSum.LightLocalCoverInit.base free))
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.space_bound (_root_.ThreeSum.LightLocalCoverInit.base free) h
  have hk := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.constant_le h
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space free h ≤ free+4*_root_.ThreeSum.LightLocalCoverResources.envelope h := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space _root_.ThreeSum.LightLocalCoverInit.base at *
    omega
  exact hm.trans (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.four_envelope_le h) free)


















end ThreeSum.LightLocalCoverInitResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts
open _root_.ThreeSum.EncodedColorWantedCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 1800000









theorem sourceBase_eq (free M h J len : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len=_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J+
      6*len+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J/M) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree
  omega















end ThreeSum.EncodedColorWantedCosts

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





theorem powers (n : ℕ) : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(464*_root_.ThreeSum.EncodedColorResources.half n)+1 := by have hh := Nat.two_pow_pos (464*_root_.ThreeSum.EncodedColorResources.half n); omega
  exact (Nat.pow_le_pow_left htwo (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)).trans (H.radixPower.trans hm)











theorem totalKeys_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hq : _root_.ThreeSum.LocalCoverBounds.outputCount (464*_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
    calc
      _ ≤ (2^(464*_root_.ThreeSum.EncodedColorResources.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) _
      _ = 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width; rw [← pow_mul]; congr 1; ring
      _ ≤ 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).1
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount
  rw [mul_pow]
  exact (Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.1 hq).trans_eq (pow_two _).symm



noncomputable section





end
end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial bounds for the retained local cover and complete global key array -/

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

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000



theorem after_cover_bound (free n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free (_root_.ThreeSum.EncodedColorResources.half n) ≤ free+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.space_bound free (_root_.ThreeSum.EncodedColorResources.half n)
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.nextFree_le_space (_root_.ThreeSum.LightLocalCoverInit.base free) (_root_.ThreeSum.EncodedColorResources.half n)
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space (_root_.ThreeSum.LightLocalCoverInit.base free) (_root_.ThreeSum.EncodedColorResources.half n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space free (_root_.ThreeSum.EncodedColorResources.half n) := le_max_right _ _
  exact ((he.trans hm).trans hs).trans (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1 free)



theorem cover_space_bound (free n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space free (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ free+20*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hlocal := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.space_bound free (_root_.ThreeSum.EncodedColorResources.half n)
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space free (_root_.ThreeSum.EncodedColorResources.half n) ≤ free+_root_.ThreeSum.EncodedColorResources.localEnvelope n at hlocal
  have henv := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1
  have hafter := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.after_cover_bound free n
  have hglobal := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.global_keys_space_bound (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free (_root_.ThreeSum.EncodedColorResources.half n)) n
  have hp3 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := Nat.le_self_pow (by decide) _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space
  apply max_le <;> nlinarith only [hlocal,henv,hafter,hglobal,hp3]

theorem key_end_bound (free n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ free+20*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd_le_space free (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.cover_space_bound free n)





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

theorem incidence_cap_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^3 := by
  have hh := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.count_le n)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap
  nlinarith only [hh]



























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
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.wanted_source_base_bound__implementation_3c5aeccc67 (free n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) ≤ free+100*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).1
  have hlen := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.incidence_cap_le n
  have hG := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.totalKeys_le n
  have hM := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  have hkey := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.key_end_bound free n
  have hp5 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^5 := Nat.le_self_pow (by decide) _
  have hp25 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 5)
  have hp35 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 5)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hlen) hG
  have hdiv := Nat.div_le_self
    (3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_eq]
  nlinarith only [hb,hlen,hG,hM,hkey,hprod,hdiv,hp5,hp25,hp35]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.wanted_source_base_bound__implementation_3c5aeccc67) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.wanted_source_base_bound__implementation_3c5aeccc67)

#print axioms solution
