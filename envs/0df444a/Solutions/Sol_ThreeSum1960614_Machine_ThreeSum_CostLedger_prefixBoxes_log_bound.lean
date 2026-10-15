-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:16:32.500651+00:00
-- url     : https://prove2.me/submissions/5ccd4c56-8dc7-4a03-a885-3133435177ba

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Switch_actual_switch_certified

local instance platformRadixNonzero_89f7b7150f (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-!
Expansion-232 analytic interface for the actual machine-source modules.
The definition bodies use the audited rational quartic parameter choice.
Closed analytic proofs supply the bounds; no program correctness contract
is assumed by this interface. Additional operational exponents must remain
the individual raw ledger costs for the universal rational-r bridge.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters

open _root_.Set











































theorem phi_half : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi (1/2)=(6631298715/1600000000 : ℝ) := by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi]
















theorem switchThreshold_upper {a : ℝ} (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a ≤ 3 := by
  have hden : 0 < 1-a := by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at ha; linarith [ha.2]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold,div_le_iff₀ hden]
  dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction] at *
  linarith [ha.2]





end ThreeSum.Parameters

end

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







































theorem microSize_even (m : ℕ) : 2 ∣ _root_.ThreeSum.Scales.microSize m := by
  exact ⟨Nat.nthRoot 3 m / 2, rfl⟩













noncomputable section







































































































































end

end ThreeSum.Scales

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





theorem accepts_expanded (J j r q : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔
      100000000*(159243801*J+500000000*j)*r^4 ≤ 500000000*(J-j)*_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial _root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator
  ring_nf













@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r ↔ q ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_mem _ _



noncomputable section

theorem depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · rw [div_le_iff₀ hJR]
    have ht : (20 : ℝ) * j ≤ 13 * J := by exact_mod_cast hj
    dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction]
    linarith

theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega

theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) =
      (159243801*(J : ℝ)+500000000*j)/(500000000*((J-j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift
  field_simp
  <;> ring

theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((q : ℝ) / r) = (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q : ℝ)/(100000000*(r : ℝ)^4) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi,_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp
  <;> ring

theorem accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold ((j : ℝ) / J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.threshold_fraction hJ hj, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r q ↔
      100000000*(159243801*(J : ℝ)+500000000*j)*(r : ℝ)^4 ≤
        500000000*((J-j : ℕ) : ℝ)*(_root_.ThreeSum1960614.Machine.ThreeSum.Switch.quarticNumerator r q : ℝ) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_expanded]
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

theorem half_fraction {r : ℕ} (hr : 0 < r) (heven : 2 ∣ r) :
    ((r / 2 : ℕ) : ℝ) / r = (1 / 2 : ℝ) := by
  have hm := Nat.div_mul_cancel heven
  have hmR : ((r / 2 : ℕ) : ℝ) * 2 = r := by exact_mod_cast hm
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  linarith

theorem candidates_nonempty {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty := by
  refine ⟨r / 2, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_iff hJ (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hJ hj) hr, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.half_fraction hr heven, _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_half]
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold_upper (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_fraction hJ hj)
  linarith

theorem switchIndex_spec {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ r / 2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J j r (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_mem (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates_nonempty hJ hj hr heven))











theorem actual_totalSize (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) * _root_.ThreeSum.Scales.muZero n := rfl

theorem actual_residual_even (n j : ℕ) : 2 ∣ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by
  exact dvd_mul_of_dvd_right (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.microSize_even (_root_.ThreeSum.Scales.inputBits n)) _

theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega

theorem actual_residual_pos {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    0 < _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hp.1 (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2

theorem residual_real_identity {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) =
      (1 - (j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  have hm := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.depth_lt hp.1 (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj)
  have hJ : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring





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





















theorem microOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < _root_.ThreeSum.CostLedger.microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes n j :=
  Nat.choose_pos (by omega)



noncomputable section

theorem microOutputs_log_bound {n : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs n : ℝ) ≤ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E * _root_.ThreeSum.Scales.muZero n * Real.log 2 := by
  have hprod := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hmR : (0 : ℝ) < _root_.ThreeSum.Scales.muZero n := by exact_mod_cast hm
  have hb := (_root_.ThreeSum.BinomialEntropy.fixed_ratio_bounds (c := 232) (r := 1)
    (by norm_num) (by norm_num) hm).2
  simp only [Nat.one_mul, Nat.cast_ofNat, Nat.cast_one] at hb
  have hc := (div_le_iff₀ hmR).mp hb
  change Real.log (((232 * _root_.ThreeSum.Scales.muZero n).choose (_root_.ThreeSum.Scales.muZero n) : ℕ) : ℝ) ≤ _
  have hid : 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E * (_root_.ThreeSum.Scales.muZero n : ℝ) * Real.log 2 =
      232 * Real.binEntropy (1 / 232) * _root_.ThreeSum.Scales.muZero n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum.Parameters.entropy
    field_simp
    <;> ring
  rw [hid]
  exact hc

theorem microPartitions_log_bound (n : ℕ) :
    Real.log (_root_.ThreeSum.CostLedger.microPartitions n : ℝ) ≤ (_root_.ThreeSum.Scales.muZero n : ℝ) * Real.log 2 := by
  have hp : (0 : ℝ) < _root_.ThreeSum.CostLedger.microPartitions n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_pos n
  have hb : (_root_.ThreeSum.CostLedger.microPartitions n : ℝ) ≤ (2 : ℝ) ^ _root_.ThreeSum.Scales.muZero n := by
    exact_mod_cast Nat.choose_le_two_pow (_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum.Scales.muZero n / 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hp hb

theorem prefixChoices_log_bound {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n j : ℝ) ≤
      (j : ℝ) * _root_.ThreeSum.Scales.muZero n * Real.log 2 * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1) := by
  have hM : (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs_pos n).ne'
  have hG : (_root_.ThreeSum.CostLedger.microPartitions n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_pos n).ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hM hG]
  have hsum := add_le_add (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs_log_bound hmu) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_log_bound n)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) j)
  nlinarith

theorem suffixBoxes_log_bound {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes n j : ℝ) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) * Real.log 2 *
        (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j)) := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_pos hmu hj
  have hrR : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by exact_mod_cast hr
  have hprod := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hprod
  have hspec := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition hj) hr (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_even n j)
  have hq : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch
    exact hspec.1.trans (Nat.div_le_self _ _)
  have hb := (_root_.ThreeSum.BinomialEntropy.log_choose_entropy_bounds
    (show _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j - _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j ≤ 232 * _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j by omega)).2
  have hratio : ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j - _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℕ) : ℝ) /
      ((232 * _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℕ) : ℝ) =
        (1 - (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j) / 232 := by
    rw [Nat.cast_sub hq, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  rw [hratio, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hid : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) * Real.log 2 *
      (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j)) =
        232 * (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) *
          Real.binEntropy ((1 - (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j) / 232) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma _root_.ThreeSum.Parameters.entropy
    field_simp
    <;> ring
  rw [hid]
  exact hb







end
end ThreeSum.CostLedger

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

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
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

section

theorem ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_log_bound__implementation_e2f4588628 {n j : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n j : ℝ) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) := by
  have hp : (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n j : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices_pos n j).ne'
  have hs : (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes n j : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes_pos n j).ne'
  have hb := add_le_add (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices_log_bound (j := j) hmu) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes_log_bound hmu hj)
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified hmu hj).2.1
  have hn : (0 : ℝ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) _root_.ThreeSum.Parameters.log_two_pos.le
  have hmul := mul_le_mul_of_nonneg_left hc hn
  have hid := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residual_real_identity hmu hj
  have hprod : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) * _root_.ThreeSum.Scales.muZero n := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize n
  have hpos := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hpos
  have hJ : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.pos_of_mul_pos_right hpos).ne'
  have hjid : (j : ℝ) * _root_.ThreeSum.Scales.muZero n =
      ((j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by rw [hprod]; field_simp
  have hcombine : (j : ℝ) * _root_.ThreeSum.Scales.muZero n * Real.log 2 * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1) +
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j : ℝ) * Real.log 2 *
        (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j)) =
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 *
        (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + (j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) -
          (1 - (j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) *
            _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.gamma ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n j : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n j)) := by
    rw [hjid, hid]
    ring
  rw [hcombine] at hb
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes, Nat.cast_mul, Real.log_mul hp hs]
  linear_combination hb + hmul
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_log_bound__implementation_e2f4588628) := (@ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_log_bound__implementation_e2f4588628)

#print axioms solution
