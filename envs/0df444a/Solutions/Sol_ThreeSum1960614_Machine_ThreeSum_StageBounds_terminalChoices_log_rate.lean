-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:42.731102+00:00
-- url     : https://prove2.me/submissions/dc584f61-2637-4f4d-b080-03db504c13cc

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Switch_terminal_fraction_exact

local instance platformRadixNonzero_a0fea91463 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
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

























noncomputable section



theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega























theorem actual_totalSize (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) * _root_.ThreeSum.Scales.muZero n := rfl



theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega



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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open scoped _root_.Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

section

theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate__implementation_18584fedd5 :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction))) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2 * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction))
  have heq : Real.log 2 * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2) =
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) := by field_simp
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hid := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residual_real_identity (by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
    (j := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) le_rfl
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminal_fraction_exact (by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)] at hid
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hid]
  ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate__implementation_18584fedd5) := (@ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate__implementation_18584fedd5)

#print axioms solution
