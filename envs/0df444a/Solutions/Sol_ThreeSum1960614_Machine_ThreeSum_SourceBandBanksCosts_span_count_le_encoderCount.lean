-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:21:44.507126+00:00
-- url     : https://prove2.me/submissions/a2cfb64b-f835-4180-8d0d-e1babb6d1d1c

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockSourceCatalogCosts_catalogCells_le_encoderCount
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul

namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostSuffixCosts
end ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandBanksCosts
end ThreeSum.SourceBandBanksCosts
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
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
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalCoverBounds


open scoped _root_.BigOperators








theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
  have hlo : 232 ^ (2 * h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
    simpa [_root_.ThreeSum.LocalCoverBounds.outputCount, show 232 * (2 * h) = 464 * h by omega] using
      _root_.ThreeSum.LocalCoverBounds.pow_le_choose_mul 232 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

























/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/













/-! ## The actual local parameters at `L=464*h` -/



































end ThreeSum.LocalCoverBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000









theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J



section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The actual local box construction is charged to the suffix binomial layer -/

namespace ThreeSum.ReportingHostSuffixCosts
open _root_.ThreeSum.ReportingHostSuffixCosts


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open scoped _root_.BigOperators

theorem choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    _root_.ThreeSum.SubsetAddress.downsetCap V cut ≤ (cut+1)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  simp only [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut,_root_.ThreeSum.SubsetAddress.layerOffset]
  calc
    _ ≤ ∑ _j ∈ Finset.range (cut+1), V.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.choose_le_cut (by have := Finset.mem_range.mp hj; omega) hhalf
    _ = _ := by simp











end ThreeSum.ReportingHostSuffixCosts

end ThreeSum1960614.Machine

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

theorem width_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) = 232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem downset_le_fullOutputs (n : ℕ) :
    _root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_le_layer (by omega)















end ThreeSum.BlockSourceSharing

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

theorem work_address (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut =
      base+count*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2)+_root_.ThreeSum.SubsetAddress.downsetCap W cut+W+2 := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.banks
  ring





















end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder







theorem host_space_add (base free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (base+free) h J=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space
    _root_.ThreeSum.LightBlockSourceHashes.space _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space
  omega

















end ThreeSum.SourceBandBankLayout

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



theorem four_le_scheduleSize (h : ℕ) : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 4*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
  have ho : 2^(2*h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
    by_cases hz : h=0
    · simp [hz,_root_.ThreeSum.LocalCoverBounds.outputCount]
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.concrete_output_gt_pow (by omega)).le
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J*
      (J*(464*h)).choose (J*(2*h)) := by
  have hl : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (464*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_global_outputs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    rw [Nat.mul_comm,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.cutoff_eq]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq,hc] at hm
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≥ _ at hm
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm



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



theorem bands_modulus_le_encoderCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_tableCount n)
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) :=
      Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_modulus_le_encoderCount n







end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts
open _root_.ThreeSum.SourceBandBanksCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress



















theorem span_eq (h J cut : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut+2)+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+J*(464*h)+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.host_space_add
    (_root_.ThreeSum.LightBlockSourceBatchLayout.work 0 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) 0 h J
  simp only [Nat.add_zero] at h
  rw [h,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.work_address]
  omega











end ThreeSum.SourceBandBanksCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
section

theorem ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount__implementation_2208ab927a {G n : ℕ} (hG : G ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) :
    G*_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hslot : G*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
    apply le_trans (b := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells n)
    · calc
        _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hG)
        _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := rfl
    · exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount n
  have hGF : G*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n :=
    (Nat.mul_le_mul_right _ hG).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount n)
  have hGK : G*_root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
    calc
      _ ≤ G*((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.downset_le_fullOutputs n)
      _ = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)*(G*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hGF
  have hGE := hG.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_le_encoderCount n)
  have hother := Nat.mul_le_mul_right
    (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) hGE
  calc
    _ = G*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+2)+
        G*_root_.ThreeSum.SubsetAddress.downsetCap (232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+
        G*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_eq,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq]
      ring
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+2*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)+7)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+
        (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+
        _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) :=
      Nat.add_le_add (Nat.add_le_add hslot hGK) hother
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor; ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount__implementation_2208ab927a) := (@ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount__implementation_2208ab927a)

#print axioms solution
