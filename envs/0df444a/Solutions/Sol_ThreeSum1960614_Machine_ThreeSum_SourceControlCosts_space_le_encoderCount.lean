-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.space_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:46:44.867587+00:00
-- url     : https://prove2.me/submissions/59678851-2a52-4f01-aafb-6800bd9b6d0e

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
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandHostCosts_space_le_encoderCount

namespace Filter
end Filter
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SourceControlCosts
end ThreeSum.SourceControlCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
end ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
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
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales
open _root_.ThreeSum.TrimScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

















noncomputable section





























theorem localLength_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  positivity



























end

end ThreeSum.TrimScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^floor(-bandShift*mu)`.
Euclidean division computes the rational exponent with bounded error.
-/

namespace ThreeSum.BandScales
open _root_.ThreeSum.BandScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology










theorem typedOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))









noncomputable section























end

end ThreeSum.BandScales

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











noncomputable section















end
end ThreeSum.CostLedger

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













theorem width_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) = 232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring



















end ThreeSum.BlockSourceSharing

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

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.HasAntidiagonal.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (232*_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hwidth : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(232*_root_.ThreeSum.Scales.muZero n)=232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum.Scales.muZero _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize
    ring
  have hcut : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum.Scales.muZero n=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := rfl
  rw [hwidth,hcut] at h
  exact h









theorem bandSize_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)
  have hr : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
    have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n-1)
    have hp := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot _root_.ThreeSum.LocalCoverBounds.rootCeiling
    omega
  exact hb.trans (hr.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.typedOutputs_le_fullOutputs n))

theorem scheduleCount_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf
  exact pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hs : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.scheduleCount_pos n
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) (Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) hs)
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bandSize_le_fullOutputs n)
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount n











end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
section

theorem ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.space_le_encoderCount__implementation_48f8b855cb {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.space base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) U D ≤
      base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n+
          (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)^2+(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1))*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+
        Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19 := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.space_le_encoderCount (base := base+3) (p := p) (U := U) (D := D) hn hNL hNR
  have he : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := hn.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.input_le_encoderCount n)
  have hp := Nat.le_mul_of_pos_right ((232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)^2+(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)) he
  have hlog : 0 ≤ Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n+1) := Nat.zero_le _
  have hlogs : 0 ≤ max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2) := Nat.zero_le _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.space _root_.ThreeSum.LightSourceControlsHost.sourceBase
  apply max_le
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControls.space _root_.ThreeSum.LightPascal.tableSize
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq]
    nlinarith
  · nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.space_le_encoderCount__implementation_48f8b855cb) := (@ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.space_le_encoderCount__implementation_48f8b855cb)

#print axioms solution
