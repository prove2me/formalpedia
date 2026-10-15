-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:42.591521+00:00
-- url     : https://prove2.me/submissions/067d2510-4404-495d-80a6-cfca49f7aa63

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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



theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))



theorem microHalf_le_self (m : ℕ) : _root_.ThreeSum.Scales.microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.root_le_self m)

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












theorem primitive_bounds (n : ℕ) :
    _root_.ThreeSum.SharedReportingBankResourceBounds.half n ≤ _root_.ThreeSum.Scales.inputBits n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ 20*_root_.ThreeSum.Scales.inputBits n ∧
    2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ _root_.ThreeSum.Scales.inputBits n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 232*_root_.ThreeSum.Scales.inputBits n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microHalf_le_self (_root_.ThreeSum.Scales.inputBits n)
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.totalSize_le_self (_root_.ThreeSum.Scales.inputBits n)
  change _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n*(2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.Scales.inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  nlinarith

theorem linear_le_magnitude (n : ℕ) : 2048*(_root_.ThreeSum.Scales.inputBits n+1) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hh : _root_.ThreeSum.Scales.inputBits n+1 ≤ 2^(_root_.ThreeSum.Scales.inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(_root_.ThreeSum.Scales.inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(_root_.ThreeSum.Scales.inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)



















end ThreeSum.SharedReportingBankResourceBounds

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



theorem input_le_magnitude (n : ℕ) : n ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hn : n ≤ 2^(_root_.ThreeSum.Scales.inputBits n+1) := by
    simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))



















end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000





theorem wanted_group_le_magnitude (n : ℕ) : _root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hc : _root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)≤2^(2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).localPower)









theorem wanted_mass_bound_le {n N NB NC : ℕ}
    (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  have hb := hB.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hc := hC.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hb) hc)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_representation_cap_le n)
  calc
    _ ≤ ((3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2 := hh
    _ = _ := by ring





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





theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^e≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)

















noncomputable section













end
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
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le__implementation_66bca200c8 {n K N NB NC : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNumeric (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC≤100*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^7 := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hJ := H.blocksBound
  have hL := H.localWidthBound
  have hG := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_group_le_magnitude n
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_representation_cap_le n
  have hmass := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_mass_bound_le hN hB hC
  have hb := hB.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hc := hC.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hprod : N*NB≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^4 := by
    calc
      _ ≤ (3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := Nat.mul_le_mul hN hb
      _ = _ := by ring
  have hprod' : N*NB*NC≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^5 := by
    calc
      _ ≤ (3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^4)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := Nat.mul_le_mul hprod hc
      _ = _ := by ring
  have hlin := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.linear_le_magnitude n
  have hcut := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.primitive_bounds n).2.2.1
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 2 7 (by decide)
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 3 7 (by decide)
  have h4 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 4 7 (by decide)
  have h5 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 5 7 (by decide)
  have h7 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 7 7 le_rfl
  have hm : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^7 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNumeric _root_.ThreeSum.LightBlockQuery.sourceCut
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le__implementation_66bca200c8) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le__implementation_66bca200c8)

#print axioms solution
