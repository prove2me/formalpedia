-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.actual_dispatch_step_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:24.898137+00:00
-- url     : https://prove2.me/submissions/7ad91d8b-78b1-41e0-9dc3-f9c82ed336be

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
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
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedTraversalCosts_expansion_le_layer
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedTraversalCosts_initial_le_layer
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedTraversalCosts_terminal_charge_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedTraversalCosts_wanted_time_le

local instance platformRadixNonzero_7e3fde3615 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightOutputDecode
end ThreeSum.LightOutputDecode
namespace ThreeSum.LightWantedDecode
end ThreeSum.LightWantedDecode
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
end ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-!
# Complete physical output-index decoding

The first pass writes the actual big-endian local-record digit array.
The second pass splits each digit, reads its retained layer mask, and
accumulates the occurrence-only source-bank code. Both output rows are
in forward original block order, including repeated record values.
-/

namespace ThreeSum.LightOutputDecode
open _root_.ThreeSum.LightOutputDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}









theorem time_bound (J V : ℕ) :
    _root_.ThreeSum.LightOutputDecode.time J V ≤ 500*(J+1)*(Nat.log 2 (V+1)+2) := by
  unfold _root_.ThreeSum.LightOutputDecode.time _root_.ThreeSum.LightOutputDecodeDigits.time _root_.ThreeSum.LightOutputDecodeStep.time
    _root_.ThreeSum.LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightOutputDecode

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



















end ThreeSum.SharedTraversalCosts

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



















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r ↔ q ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_mem _ _



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
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode
open _root_.ThreeSum.LightWantedDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}









theorem time_bound (J V : ℕ) :
    _root_.ThreeSum.LightWantedDecode.time J V ≤ 800*(J+1)*(Nat.log 2 (V+1)+2) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.time_bound J V
  unfold _root_.ThreeSum.LightWantedDecode.time _root_.ThreeSum.LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightWantedDecode

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
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



















theorem wanted_decode_log_le (n : ℕ) :
    Nat.log 2 (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n+1) ≤ 8192*(_root_.ThreeSum.Scales.inputBits n+1)+1 := by
  have hp : 1≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n := Nat.one_le_pow _ _ (by decide)
  have hb : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n+1 ≤ 2^(8192*(_root_.ThreeSum.Scales.inputBits n+1)+1) := by
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV at *
    rw [pow_succ]
    omega
  exact (Nat.log_mono_right (b := 2) hb).trans (by simp)



end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000





theorem residual_eq (n k : ℕ) :
    _root_.ThreeSum.LightBlockQuery.residualSize (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) k=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := rfl

theorem group_eq (n : ℕ) : _root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedTraversalCosts.half n)=_root_.ThreeSum.CostLedger.microPartitions n := by
  have hsize : 2*_root_.ThreeSum.SharedTraversalCosts.half n=_root_.ThreeSum.Scales.muZero n := rfl
  have hhalf : _root_.ThreeSum.Scales.muZero n/2=_root_.ThreeSum.SharedTraversalCosts.half n := by omega
  simp only [_root_.ThreeSum.LocalCoverBounds.groupSize,_root_.ThreeSum.CostLedger.microPartitions,hsize,hhalf]

theorem terminal_le_blocks (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.terminal_le_blocks n



theorem switch_le_half {n k : ℕ} (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k/2 := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty
    (h := _root_.ThreeSum.SharedTraversalCosts.half n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (k := k) hk
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_mem hn)).1
  have hr : _root_.ThreeSum.SharedReportingBankLevels.residual (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) k=_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq]
    unfold _root_.ThreeSum.SharedReportingBankLevels.residual _root_.ThreeSum.LightBlockQuery.residualSize
    ring
  rw [hr] at hm
  exact hm







theorem initial_le_scaled {n : ℕ} (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hD : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.CatalogScales n D) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0 := by
  have ht : (D 0).t ≤ _root_.ThreeSum.LightBlockQuery.residualSize (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) 0/2 := by
    rw [hD 0 (by omega),_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.switch_le_half (by omega)
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_layer D (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_le_blocks n) ht
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead,_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms,_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq,hD 0 (by omega)] using hh

theorem level_unit_le_scaled {n : ℕ} (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hD : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.CatalogScales n D) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.levelUnit (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n := by
  have hterm (k : ℕ) (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPositiveExpand.time (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) k (D (k+1)).t+200 ≤
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n (k+1) := by
    have hkJ := hk.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_le_blocks n)
    have hkp : k+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n := hk
    have ht : (D (k+1)).t ≤ _root_.ThreeSum.LightBlockQuery.residualSize (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (k+1)/2 := by
      rw [hD (k+1) hkp,_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq]
      exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.switch_le_half hkp
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.expansion_le_layer hkJ ht
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead,_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms,_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.group_eq,_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_eq,hD (k+1) hkp] using hh
  have hs : (∑ k ∈ range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n), _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n (k+1)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms
    rw [sum_range_succ']
    omega
  calc
    _ ≤ ∑ k ∈ range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n),
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n (k+1) :=
      sum_le_sum (fun k hk => hterm k (mem_range.mp hk))
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum.CostLedger.microPartitions n*
        (∑ k ∈ range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n), _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n (k+1)) := (mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hs

theorem terminal_charge_le_scaled (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalFrontier.charge (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)+240 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)).1
  have hpow := Nat.pow_le_pow_right hp (by decide : 2 ≤ 4)
  have hscalar : 31000*_root_.ThreeSum.SharedTraversalCosts.size (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)^2 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n :=
    Nat.mul_le_mul (by decide) hpow
  have he : 2^((_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)*(2*_root_.ThreeSum.SharedTraversalCosts.half n))=_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n := rfl
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hscalar)

theorem search_unit_le_scaled {n : ℕ} (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hD : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.CatalogScales n D) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.level_unit_le_scaled D hD
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_charge_le_scaled n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit
  nlinarith only [hl,ht]





open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section











end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000



theorem dispatch_time_le (c n : ℕ) :
    _root_.ThreeSum.LightReportingWantedDecodeAccess.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)
        (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.time (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)+c ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c n := by
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)
    (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_decode_log_le n
  have hb := hd.trans (Nat.mul_le_mul_left (800*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n+1))
    (show Nat.log 2 (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n+1)+2 ≤
      8192*(_root_.ThreeSum.Scales.inputBits n+1)+3 by omega))
  unfold _root_.ThreeSum.LightReportingWantedDecodeAccess.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.time _root_.ThreeSum.LightNatPower.time _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead
  omega









open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section









end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.actual_dispatch_step_le__implementation_fbcb06516e {n NL NR old threshold : ℕ}
    {cfg : _root_.ThreeSum.LightReportingWantedDispatch.Config}
    (hcH : cfg.h=_root_.ThreeSum.SharedTraversalCosts.half n) (hcJ : cfg.J=_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)
    (p : ℕ) (shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (left right : ℕ→ℤ)
    (eL : Fin NL≃B) (eR : Fin NR≃C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i))
    (hvR : ∀ i : Fin NR, right i.val=c (eR i))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) α) (D : ℕ→_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog)
    (hD : _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.CatalogScales n D)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)∣
      (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time cfg (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold I w D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n))+300 ≤
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead 4800 n+
          if threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 0 else
            _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n)) := by
  dsimp only
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.wanted_time_le (old := old) (threshold := threshold) p shift A B C a b c
    left right eL eR hvL hvR w D (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.terminal_le_blocks n) hkey
  have hi := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_scaled D hD
  have hw := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.search_unit_le_scaled D hD)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatch_time_le 4800 n
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold I w D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) ≤
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)+
      (if threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 0 else
        _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w*_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.searchUnit (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n) D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n)) at hr
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time cfg (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold I w D (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n))+300 ≤
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0+_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead 4800 n+
      if threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w then 0 else
        _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead n*(_root_.ThreeSum.CostLedger.microPartitions n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n+_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time
  rw [hcH,hcJ]
  by_cases hg : threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w
  · simp only [if_pos hg] at hr ⊢
    omega
  · simp only [if_neg hg] at hr ⊢
    omega
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.actual_dispatch_step_le__implementation_fbcb06516e.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.actual_dispatch_step_le__implementation_fbcb06516e.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
