-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:22:46.427103+00:00
-- url     : https://prove2.me/submissions/886ddf9f-4cd3-4d61-9b11-151166dcf8e9

import Aesop
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales

section

theorem ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate__implementation_8948a7bd93 :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n : ℝ) / Real.log n) atTop
      (𝓝 ((-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon)) := by
  have h := (_root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_limits.2.2.2.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto
  have heq : (Real.log 2 * ((-_root_.ThreeSum1960614.beta) * _root_.ThreeSum1960614.epsilon)) *
      (1 / Real.log 2) = (-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon := by
    dsimp [_root_.ThreeSum1960614.beta,_root_.ThreeSum1960614.epsilon,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon]
    field_simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandExponent,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,_root_.ThreeSum.Scales.microSize,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandDivisor,_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize,_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.blockCount,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize]
  field_simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate__implementation_8948a7bd93) := (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate__implementation_8948a7bd93)

#print axioms solution
