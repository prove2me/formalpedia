-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:29:34.228634+00:00
-- url     : https://prove2.me/submissions/92fad24b-4416-4ac6-ac77-f406d093b0f8

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

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













































































































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.Filter
open _root_.Real
open scoped _root_.Topology
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

section

theorem ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto__implementation_e8a6a078ba :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E)) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.BinomialEntropy.output_table_rate.comp _root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_tendsto_atTop
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E * (Real.log 2 * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2)) =
      2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.muZero n : ℝ) ≠ 0 := by exact_mod_cast (by omega : muZero n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs, Nat.cast_pow, Real.log_pow]
  have hmu : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) * _root_.ThreeSum.Scales.muZero n := by
    simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum.Scales.muZero]
  rw [hmu]
  field_simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto__implementation_e8a6a078ba) := (@ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto__implementation_e8a6a078ba)

#print axioms solution
