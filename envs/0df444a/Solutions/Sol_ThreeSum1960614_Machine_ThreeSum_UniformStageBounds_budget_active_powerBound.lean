-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:16:55.579862+00:00
-- url     : https://prove2.me/submissions/4c49fc2a-d8e9-4a21-90e4-4464dc775378

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_CostLedger_queryTerms_log_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_HierarchyScales_hierarchyEnvelope_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_MassScales_falseNumerator_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_representationBound_log_rate

local instance platformRadixNonzero_92f1eaaa50 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds
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
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds

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





















































noncomputable section

























theorem muZero_tendsto_atTop : Tendsto _root_.ThreeSum.Scales.muZero atTop atTop :=
  _root_.ThreeSum.Scales.microSize_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop

theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (_root_.ThreeSum.Scales.muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (_root_.ThreeSum.Scales.microSize_square_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.muZero]
  field_simp







theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [_root_.ThreeSum.Scales.localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h



/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum.Scales.localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_log_ratio_tendsto_zero C) hd





























































































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

























noncomputable section



























theorem actual_totalSize (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) * _root_.ThreeSum.Scales.muZero n := rfl



theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega









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













theorem terminalDepth_le_mu {n : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  have hprod := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (show 1 ≤ _root_.ThreeSum.Scales.muZero n by omega)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition (n := n) (j := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) le_rfl
  rw [Nat.mul_one, ← _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hc
  omega

noncomputable section





theorem allQueryTerms_envelope {n : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n : ℝ) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))
        (9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * Real.log 2) n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n + 1),
        Real.exp ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 *
          (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + 9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * Real.log 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms_log_bound hmu (by simpa using hj))
    _ = (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n + 1 : ℝ) *
        Real.exp ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 *
          (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + 9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * Real.log 2) := by simp
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))
        (9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * Real.log 2) n := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.terminalDepth_le_mu hmu) 1





theorem eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    ((div_lt_iff₀ hlog).mp hn).le



theorem allQueryTerms_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms n : ℝ) ≤
      (n : ℝ) ^ (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + d) := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate
    (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))
      (9 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * Real.log 2)) hd
  filter_upwards [he, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.allQueryTerms_envelope (by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)).trans hn





theorem microPartitions_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum.CostLedger.microPartitions n : ℝ) ≤ (n : ℝ) ^ d := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_subpolynomial 1 hd,
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hpow : _root_.ThreeSum.Scales.muZero n ≤ _root_.ThreeSum.Scales.muZero n ^ 2 := by nlinarith
  have hc : _root_.ThreeSum.CostLedger.microPartitions n ≤ _root_.ThreeSum.Scales.localSearch 1 n := by
    exact (Nat.choose_le_two_pow _ _).trans (by simpa [_root_.ThreeSum.Scales.localSearch] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow)
  exact (show (_root_.ThreeSum.CostLedger.microPartitions n : ℝ) ≤ _root_.ThreeSum.Scales.localSearch 1 n by exact_mod_cast hc).trans hn

























end
end ThreeSum.HierarchyScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales
open _root_.ThreeSum.MassScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000









theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos hn
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound
  positivity



theorem scoreLoss_pos (k n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
  unfold _root_.ThreeSum.Scales.primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < _root_.ThreeSum.Scales.candidateCount n := by
  filter_upwards [_root_.ThreeSum.Scales.actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn

theorem falseNumerator_eventually_pos (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_pos (by omega : 0 < n)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scoreLoss_pos k n
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.primeLoss_pos n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator
  positivity

noncomputable section

























theorem falseMajorant_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate k).sub _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto
  have hid : (2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_eventually_pos k] with n hn
  have hN : (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n).ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, Real.log_div hN hR, sub_div]



theorem falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n ≤ (n : ℝ) ^ (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) + d) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant_log_rate k) hd





end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds
open _root_.ThreeSum.StageBounds


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





















noncomputable section



namespace PowerBound
open _root_.ThreeSum.StageBounds.PowerBound


theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a :=
  fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio hf hd



theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring







end PowerBound

































end
end ThreeSum.StageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds
open _root_.ThreeSum.UniformStageBounds


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
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000











noncomputable section





theorem falseBudget_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  intro d hd
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant_eventually_le k hd] with n hn
  have hb : (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, le_div_iff₀ (show (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
  exact hb.trans hn



























end
end ThreeSum.UniformStageBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds

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
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open scoped _root_.Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds

section

theorem ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound__implementation_e4d3070ecd (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.activeCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k))
      (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hG : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.CostLedger.microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.microPartitions_subpolynomial hd
  have hQ : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allQueryTerms (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) :=
    fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.allQueryTerms_eventually_le hd
  have hh := (((_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget_powerBound k).mul
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa + 0) +
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    ring
  rw [heq] at hh
  exact hh
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound__implementation_e4d3070ecd) := (@ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound__implementation_e4d3070ecd)

#print axioms solution
