-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaled_word_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:01:28.222978+00:00
-- url     : https://prove2.me/submissions/4956ceff-2b9c-4e09-a7a9-d332d3dc83ad

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
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
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
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
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

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

















end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000




















theorem band_le_magnitude (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) := by
    rw [show _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)=232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n from _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).widthPower)

theorem prefix_storage_le_magnitude (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixStorage (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2 := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hmul := Nat.mul_le_mul (H.levelsBound.trans (Nat.le_succ _)) (Nat.add_le_add_right H.prefixBound 1)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixStorage,pow_two] using hmul











end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaled_word_le__implementation_da2cdf7251 (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaledWord n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.envelope n := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hJ := H.blocksBound
  have hK := H.levelsBound
  have hN := H.prefixBound
  have hC := H.occurrence
  have hP := H.localPower
  have hE := H.pairsPower
  have hWP := H.widthPower
  have hIP := H.indexPower
  have hD := H.depthWord
  have hG := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.band_le_magnitude n
  have hS := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefix_storage_le_magnitude n
  have hspan := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude n
  have hpower : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hWP
  have hlocal : 2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hP
  have hv := Nat.mul_le_mul hlocal H.radixPower
  have hkeyMul := Nat.mul_le_mul hlocal hv
  have hkeys : _root_.ThreeSum.LightRadixKeys.word (2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤
      (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3+2*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1 := by
    unfold _root_.ThreeSum.LightRadixKeys.word _root_.ThreeSum.LightRadixRows.word
    nlinarith
  have hindexMul := Nat.mul_le_mul (Nat.pow_le_pow_left hpower 2) (Nat.add_le_add_right hIP 1)
  have hindex : _root_.ThreeSum.LightReportingSortedCatalog.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (2^(2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))) ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)+3*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+2 := by
    unfold _root_.ThreeSum.LightReportingSortedCatalog.word _root_.ThreeSum.LightReportingPackKeys.word
    omega
  have hwidth := Nat.mul_le_mul hW hWP
  have hv1 := Nat.mul_le_mul hpower hG
  have hv2 := Nat.mul_le_mul hv1 hv1
  have hv3 := Nat.mul_le_mul hpower hv2
  have hcontrol := Nat.mul_le_mul_right n hC
  have hswitch := Nat.pow_le_pow_left H.switchBase 96
  let R := (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^5*(n+1)^2
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hp : 1 ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have dominates {e : ℕ} (he : e ≤ 5) : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^e ≤ R :=
    (Nat.pow_le_pow_right (by omega) he).trans (Nat.le_mul_of_pos_right _ hn)
  have smaller {e : ℕ} (he : e ≤ 5) : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^e ≤ R :=
    (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (dominates he)
  have oneR : 1 ≤ R := by simpa only [pow_zero] using dominates (e := 0) (by decide)
  have magR : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n ≤ R := by simpa only [pow_one] using smaller (e := 1) (by decide)
  have nquad : n ≤ (n+1)^2 := by nlinarith only [Nat.zero_le n]
  have nR : n ≤ R := nquad.trans (Nat.le_mul_of_pos_left _ hp)
  have mnR : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*n ≤ R := Nat.mul_le_mul
    ((Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)) nquad
  have controlR := hcontrol.trans mnR
  have storageR := hS.trans (dominates (e := 2) (by decide))
  have spanR := hspan.trans (Nat.mul_le_mul_left 100 (dominates (e := 3) (by decide)))
  have cubeR := smaller (e := 3) (by decide)
  have keysR : _root_.ThreeSum.LightRadixKeys.word (2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 4*R := by omega
  have indexProductR : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1) ≤ R := by
    calc
      _ ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ _) 2)
      _ = (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^3 := by ring
      _ ≤ R := dominates (by decide)
  have indexR : _root_.ThreeSum.LightReportingSortedCatalog.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (2^(2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))) ≤ 6*R := by omega
  have widthR : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1) ≤ R := by
    exact hwidth.trans (by simpa only [pow_two] using smaller (e := 2) (by decide))
  have valuesR : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))*
      ((2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)*
       (2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) ≤ R := by
    exact hv3.trans (by simpa only [show _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*((_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n))=
      (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^5 by ring] using smaller (e := 5) (by decide))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaledWord _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.envelope
  apply Nat.add_le_add _ hswitch
  rw [show _root_.ThreeSum.SharedReportingBankResourceBounds.polynomialPart n=5000*R by dsimp [R,_root_.ThreeSum.SharedReportingBankResourceBounds.polynomialPart]; ring]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.control _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.stateWord
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaled_word_le__implementation_da2cdf7251) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.scaled_word_le__implementation_da2cdf7251)

#print axioms solution
