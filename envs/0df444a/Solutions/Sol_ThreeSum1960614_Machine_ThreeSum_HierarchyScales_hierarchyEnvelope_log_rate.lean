-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:48:21.177381+00:00
-- url     : https://prove2.me/submissions/15dc6f71-a527-4b3f-8196-889d04443bef

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







theorem log_mu_add_one_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n + 1 : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (_root_.ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 1) (by norm_num)).comp _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop
  have hh := he.mul _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hmu : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n ≠ 0)
  simp only [Function.comp_def, Nat.cast_one, one_mul]
  field_simp







































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

theorem ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate__implementation_9d6882ba26 (C B : ℝ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope C B n) / Real.log n) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*C)) := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2 * C)
  have hid : Real.log 2*C*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon/Real.log 2)=_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*C := by field_simp
  rw [hid] at hm
  have hc := _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul B
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.log_mu_add_one_rate.add (hm.add hc)
  simp only [mul_zero, add_zero, zero_add] at hh
  convert hh using 1
  funext n
  have hp : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n + 1 : ℝ) ≠ 0 := by positivity
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope, Real.log_mul hp (Real.exp_ne_zero _), Real.log_exp,
    Pi.inv_apply, add_div]
  ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate__implementation_9d6882ba26) := (@ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate__implementation_9d6882ba26)

#print axioms solution
