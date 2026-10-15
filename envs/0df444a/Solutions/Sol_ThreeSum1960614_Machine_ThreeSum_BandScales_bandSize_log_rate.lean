-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:34.265524+00:00
-- url     : https://prove2.me/submissions/b44c9e41-eaca-4191-9b96-a217e2c76c94

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandDivisor_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandRoot_log_rate

local instance platformRadixNonzero_0ef3a74f85 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


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

namespace ThreeSum1960614.Machine

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^floor(-bandShift*mu)`.
Euclidean division computes the rational exponent with bounded error.
-/

namespace ThreeSum.BandScales
open _root_.ThreeSum.BandScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology




















noncomputable section











theorem unroundedBand_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n := by
  have hR : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_pos n
  have hD : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n
  exact div_pos hR hD

theorem unroundedBand_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate.sub _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate
  have heq : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - (-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon =
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with n
  have hR : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_pos n
  have hD : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand, Real.log_div hR.ne' hD.ne', sub_div]

theorem unroundedBand_eventually_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n := by
  have hpos : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    exact mul_pos _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon_positive (by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift]; linarith)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_pos n).le).mp hb).le

theorem bandSize_ge_unrounded (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) := by
  have hD : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n
  have hl : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
    exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_mul_bounds n).1
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand, div_le_iff₀ hD]
  simpa only [mul_comm] using hl

theorem bandSize_eventually_le_twice_unrounded :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) ≤ 2 * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_eventually_ge_one] with n hn
  have hD : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n
  have hu : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by
    exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_mul_bounds n).2
  have hb : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand n + 1 := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand]
    have heq : ((_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n =
        (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n + 1 := by field_simp
    rw [← heq]
    apply (lt_div_iff₀ hD).mpr
    simpa only [mul_comm] using hu
  linarith



end

end ThreeSum.BandScales

end ThreeSum1960614.Machine

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

theorem ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate__implementation_46dfa1a5bf :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have herr := _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_log_rate.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_log_rate hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_eventually_le_twice_unrounded, eventually_ge_atTop (1 : ℕ)] with n hn hge
    have hpos : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    have hlog := Real.log_le_log hpos hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.unroundedBand_pos n).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast hge))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate__implementation_46dfa1a5bf) := (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate__implementation_46dfa1a5bf)

#print axioms solution
