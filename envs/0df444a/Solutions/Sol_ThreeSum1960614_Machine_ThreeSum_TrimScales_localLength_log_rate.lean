-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:15.266297+00:00
-- url     : https://prove2.me/submissions/985cfcb1-bfc0-47d6-b820-ad48ec9b2dbf

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_localPrime_sq_le_power

local instance platformRadixNonzero_59476344ae (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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



























theorem localPrime_log2_sq_le (h : ℕ) :
    Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ^ 2) ≤ 4 + 466 * h := by
  rw [Nat.log2_eq_log_two]
  have hm := Nat.log_mono_right (b := 2) (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localPrime_sq_le_power h)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hm

theorem localLength_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  positivity

theorem localLength_quadratic_bound (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h ≤ 2 ^ 19 * (h + 1) ^ 2 := by
  have hlog := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localPrime_log2_sq_le h
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h ≤ 320 * (2 * h + 1) * (466 * h + 5) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
    exact Nat.mul_le_mul_left _ (by omega)
  norm_num
  nlinarith [hb]

























end

end ThreeSum.TrimScales

end ThreeSum1960614.Machine

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

theorem ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate__implementation_7b507a5e32 :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
  have hlog := _root_.ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero (c := 1) (by norm_num)
  have hinv := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hu := (hinv.const_mul (19 / 2 : ℝ)).add (hlog.div_const (Real.log 2))
  simp only [mul_zero, zero_div, zero_add] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun h =>
      div_nonneg (Real.log_natCast_nonneg _) (by positivity))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hlen : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos h
    have hb : (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h : ℝ) ≤ (2 : ℝ) ^ 19 * (h + 1) ^ 2 := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_quadratic_bound h
    have hlogb := Real.log_le_log hlen hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlogb
    have hd := div_le_div_of_nonneg_right hlogb (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    apply le_of_le_of_eq hd
    simp only [one_mul, Pi.inv_apply, Nat.cast_ofNat]
    field_simp
    ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate__implementation_7b507a5e32) := (@ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate__implementation_7b507a5e32)

#print axioms solution
