-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:17.157766+00:00
-- url     : https://prove2.me/submissions/6a046976-cb1c-454f-b259-7d4907936a0e

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_record_scalars_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds

namespace ThreeSum1960614.Machine

/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false











theorem wanted_work_eq (dst h J K N NB NC : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work=
      dst+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork h J K N NB NC := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout _root_.ThreeSum.ReportingHostWantedLayout.make _root_.ThreeSum.ReportingHostFrontierLayout.slot
    _root_.ThreeSum.ReportingHostWantedLayout.root _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  ring

theorem wanted_work_formula (h J K N NB NC : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork h J K N NB NC=44+3*J+
      (K+1)*(4+2*_root_.ThreeSum.ReportingHostWantedLayout.capacityBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) (_root_.ThreeSum.LocalCoverBounds.groupSize h))+
      5*_root_.ThreeSum.LocalCoverBounds.groupSize h+12*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+5*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout _root_.ThreeSum.ReportingHostWantedLayout.make _root_.ThreeSum.ReportingHostFrontierLayout.slot
    _root_.ThreeSum.ReportingHostWantedLayout.root _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  ring













section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







end Raw
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000













theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedCells (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_le hK hN hB hC
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le hK hN hB hC
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scratch_le n
  have h9 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^9≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^7≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedCells _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega









noncomputable section





theorem wanted_buffers_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedBuffers lim dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers ((Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_cells_le hK hN hB hC) dst).trans hok.cells)







end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Individual selector bounds from the proved wanted Need -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000







theorem wanted_access_output_le {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+20≤lim.space := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_eq dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_formula (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  unfold _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  omega





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
set_option maxHeartbeats 2100000
set_option maxRecDepth 16000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok__implementation_726d416427 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+8≤dst) (hcounter : counter+2≤dst)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.space (_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) dst cover counter
      (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K≤lim.space := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_access_output_le hK hN hB hC hok
  have hw := H.numeric
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_eq dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_formula (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  have hcell := hok.cells
  change dst+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.space at hcell
  have hn : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.numericExtra (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K≤lim.space :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_scalars_le hK).trans (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.space
  apply max_le
  · exact max_le ha (by omega)
  · exact max_le (max_le (by omega) (by omega)) hn
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok__implementation_726d416427) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok__implementation_726d416427)

#print axioms solution
