-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:14.122727+00:00
-- url     : https://prove2.me/submissions/d720aa58-1f9c-4694-afb6-4305e86085db

import Aesop
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

local instance platformRadixNonzero_ca3a51a097 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales

section

theorem ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate__implementation_daa8552980 {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * a)) := by
  have hl := hf.comp (_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : a * (Real.log 2 * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2)) = _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * a := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) at hn
  have hn0 : (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf, Nat.cast_pow, Real.log_pow]
  have hmu : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) *
      (2 * _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum.Scales.microSize, _root_.ThreeSum.Scales.microHalf]
  rw [hmu]
  field_simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate__implementation_daa8552980) := (@ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate__implementation_daa8552980)

#print axioms solution
