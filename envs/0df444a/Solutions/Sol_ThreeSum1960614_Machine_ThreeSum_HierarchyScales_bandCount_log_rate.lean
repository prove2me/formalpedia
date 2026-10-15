-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:12.84944+00:00
-- url     : https://prove2.me/submissions/cefce029-b2d4-4ea4-a0f7-db431fa3c628

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandSize_log_rate

local instance platformRadixNonzero_c9f5e584e1 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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















noncomputable section



































theorem unroundedBandCount_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n := by
  exact div_pos (by exact_mod_cast hn) (by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)

theorem unroundedBandCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n) / Real.log n) atTop
      (𝓝 (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := hone.sub _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate
  change Tendsto (fun n : ℕ => (1 : ℝ) - Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) / Real.log n)
    atTop (𝓝 (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) at hh
  change Tendsto _ _ (𝓝 (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbR : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n).ne'
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount, Real.log_div hnR hbR, sub_div, div_self hlog]

theorem bandCount_ge_unrounded (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n : ℝ) := by
  have hb : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount, div_le_iff₀ hb]
  have hn : (n : ℝ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
    by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
  simpa only [mul_comm] using hn

theorem unroundedBandCount_eventually_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n := by
  have ha : (0 : ℝ) < 1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
    dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon]
    linarith
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_log_rate.eventually (lt_mem_nhds ha)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_pos (by omega : 0 < n)).le).mp hb).le

theorem bandCount_eventually_le_twice :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n : ℝ) ≤ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_eventually_ge_one] with n hn
  have hb : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  have hu : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n < (n : ℝ) + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n :=
    by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).2
  have hsmall : (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount n + 1 := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount]
    have hid : (n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n + 1 =
      ((n : ℝ) + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by field_simp
    rw [hid, lt_div_iff₀ hb]
    simpa only [mul_comm] using hu
  linarith



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

theorem ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate__implementation_8947eb21b5 :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n : ℝ) / Real.log n) atTop
      (𝓝 (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have he := _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_log_rate.add he
  simp only [mul_zero, add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_log_rate hh
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_pos (by omega)) (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  · filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_eventually_le_twice, eventually_ge_atTop (2 : ℕ)] with n hn hge
    have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
      lt_of_lt_of_le (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_pos (by omega)) (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_ge_unrounded n)
    have hlog := Real.log_le_log hp hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.unroundedBandCount_pos (by omega : 0 < n)).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate__implementation_8947eb21b5) := (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate__implementation_8947eb21b5)

#print axioms solution
