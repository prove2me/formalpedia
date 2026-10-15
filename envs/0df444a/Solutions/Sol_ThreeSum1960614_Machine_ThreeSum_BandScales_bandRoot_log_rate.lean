-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:40.66889+00:00
-- url     : https://prove2.me/submissions/021f9538-477f-4c70-8930-43114bcf1166

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_typedOutputs_log_ratio_tendsto

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










theorem typedOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))









noncomputable section



theorem bandRoot_log_interval (n : ℕ) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) ≤ 2 * Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) ∧
      2 * Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) ≤ Real.log 4 + Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) := by
  have hM : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n
  have hr : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_pos n
  have hlo : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) ^ 2 := by
    exact_mod_cast _root_.ThreeSum.LocalCoverBounds.le_rootCeiling_sq (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n)
  have hup : (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) ^ 2 ≤ 4 * (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) := by
    exact_mod_cast _root_.ThreeSum.LocalCoverBounds.rootCeiling_sq_le_four (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n)
  constructor
  · simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hM hlo
  · simpa only [Real.log_pow, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hM.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (bandRoot n : ℝ) ^ 2) hup



















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

theorem ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate__implementation_bc1f44df3f :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E)) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto.div_const 2
  have heq : 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E / 2 = _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E := by ring
  rw [heq] at hl
  have herr := _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4 / 2)
  have hu := hl.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_interval n).1
    apply (le_div_iff₀ hp).mpr
    have he : (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) / Real.log n / 2) * Real.log n =
        Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) / 2 := by field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_interval n).2
    apply (div_le_iff₀ hp).mpr
    simp only [Pi.inv_apply]
    have he : (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) / Real.log n / 2 +
        (Real.log 4 / 2) * (Real.log n)⁻¹) * Real.log n =
        (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℝ) + Real.log 4) / 2 := by field_simp
    rw [he]
    linarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate__implementation_bc1f44df3f) := (@ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate__implementation_bc1f44df3f)

#print axioms solution
