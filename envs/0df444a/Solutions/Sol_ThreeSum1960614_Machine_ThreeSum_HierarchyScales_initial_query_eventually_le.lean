-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:26:03.800629+00:00
-- url     : https://prove2.me/submissions/7ffb8242-4cbb-4b0f-8a03-d6edce533d42

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
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

local instance platformRadixNonzero_cae308815e (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

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
theorem phi_initial : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta := by
  norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta]















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











































theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2 :=
    div_pos _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon_positive _root_.ThreeSum.Parameters.log_two_pos
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.pos_mul_atTop hpos _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn











end

end ThreeSum.TrimScales

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

theorem switchIndex_le {J j r q : ℕ} (hq : q ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ q := by
  have h : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq

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







end
end ThreeSum.Switch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales
open _root_.ThreeSum.HierarchyScales


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





theorem initialCap_bounds (r : ℕ) :
    40409899*r ≤ 1000000000*_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r ∧
      1000000000*_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r < 40409899*r+1000000000 := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := 1000000000) (b := 40409899*r)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r) (by norm_num)).mp le_rfl
  · have h := Nat.div_mul_le_self (40409899*r+1000000000-1) 1000000000
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap, Nat.ceilDiv_eq_add_pred_div]
    omega

theorem initialCap_accepted (J r : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts J 0 r (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r) := by
  by_cases hJ : J=0
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts,
      _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor,hJ]
  by_cases hr : r=0
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts,
      _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left,_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial,hr]
  have hp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hc : (40409899 : ℝ)*r ≤ 1000000000*_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap_bounds r).1
  have ht : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r : ℝ)/r := by
    rw [le_div_iff₀ hp]
    dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta]
    linarith
  have ht0 : 0 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta := by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta]
  have hphi : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi ((_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r : ℝ)/r) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi
    gcongr
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.accepts_iff (by omega) (by omega) (by omega)]
  simpa only [Nat.cast_zero,zero_div,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold,add_zero,sub_zero,div_one] using
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi_initial.le.trans hphi

theorem initialIndex_le_cap (J : ℕ) {r : ℕ} (hr : 50 ≤ r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J 0 r ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap r := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_le
  apply _root_.ThreeSum1960614.Machine.ThreeSum.Switch.mem_candidates.mpr
  refine ⟨?_, _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap_accepted J r⟩
  have h := (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap_bounds r).2
  omega

theorem residual_zero (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n 0 = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize, Nat.sub_zero, _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize]



noncomputable section























theorem initial_ratio_le {n : ℕ} (hmu : 50 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n 0 : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialIndex_le_cap (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) hmu
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap_bounds (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)).2
  have hq' : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n 0 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initialCap (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch, _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.residual_zero] using hq
  have hbound : (1000000000 : ℝ)*_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n 0 < 40409899*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1000000000 := by
    exact_mod_cast lt_of_le_of_lt (Nat.mul_le_mul_left 1000000000 hq') hc
  have hmuR : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by exact_mod_cast (by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
  rw [div_le_iff₀ hmuR]
  have hid : (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n =
      (40409899/1000000000 : ℝ)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+1 := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta
    field_simp
  rw [hid]
  linarith

theorem initial_upper_mem {n : ℕ} (hmu : 50 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
  have hm : (50 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by exact_mod_cast hmu
  have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by linarith
  have hu : 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) hm
  constructor
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta; positivity
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta; linarith

theorem initial_query_log_bound {n : ℕ} (hmu : 50 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0 : ℝ) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * _root_.ThreeSum.Parameters.entropy (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) := by
  have hm : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by omega
  have ht := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_switch_certified (j := 0) hm (by omega)).1
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.residual_zero] at ht
  have hupper := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_upper_mem hmu
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (by simpa only [one_div] using ht)
    (by simpa only [one_div] using hupper) (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_ratio_le hmu)
  have hprod := hm
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hprod
  have hq := (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition (n := n) (j := 0) (by omega))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_pos hm (by omega)) (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_residual_even n 0)).1
  have hb := (_root_.ThreeSum.BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  change Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0 : ℝ) ≤
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n 0 : ℝ) * Real.binEntropy ((_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n 0 : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n 0) at hb
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.residual_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n))
  have hid : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * _root_.ThreeSum.Parameters.entropy (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) =
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.binEntropy (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) := by
    unfold _root_.ThreeSum.Parameters.entropy
    field_simp
  rw [hid]
  exact hb.trans hmul

theorem initial_entropy_tendsto :
    Tendsto (fun n : ℕ => _root_.ThreeSum.Parameters.entropy (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ))) atTop
      (𝓝 (_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta)) := by
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_cast_tendsto_atTop.inv_tendsto_atTop.const_add _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta
  simp only [add_zero] at hu
  have hc : Continuous _root_.ThreeSum.Parameters.entropy := Real.binEntropy_continuous.div_const _
  simpa only [Function.comp_def, one_div, Pi.inv_apply] using hc.continuousAt.tendsto.comp hu

















end
end ThreeSum.HierarchyScales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales

open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology
open scoped _root_.BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales

section

theorem ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le__implementation_5a8ded737e {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0 : ℝ) ≤
      (n : ℝ) ^ (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + d) := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2)
  have hid : Real.log 2*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon/Real.log 2)=_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon := by field_simp
  rw [hid] at hm
  have hh := hm.mul _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_entropy_tendsto
  have hrate : Tendsto
      (fun n : ℕ => ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * _root_.ThreeSum.Parameters.entropy (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + 1 / (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ))) /
        Real.log n) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta)) := by
    convert hh using 1
    · funext n
      ring
  have hs := hrate.eventually (gt_mem_nhds (by linarith : epsilon*entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta < epsilon*entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta + d))
  filter_upwards [hs, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 50),
    eventually_ge_atTop (2 : ℕ)] with n hn hmu hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_log_bound hmu
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    (hb.trans ((div_lt_iff₀ hlog).mp hn).le)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le__implementation_5a8ded737e) := (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le__implementation_5a8ded737e)

#print axioms solution
