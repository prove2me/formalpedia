-- Prove2me | solution 1 for ThreeSum.BandScales.bandRoot_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:21.587934+00:00
-- url     : https://prove2.me/submissions/e26555c8-cbe2-460d-8034-ca2e658bbc07

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Scales_typedOutputs_log_ratio_tendsto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Scales
end ThreeSum.Scales

section


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology











theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section



theorem bandRoot_log_interval (n : ℕ) :
    Real.log (typedOutputs n : ℝ) ≤ 2 * Real.log (bandRoot n : ℝ) ∧
      2 * Real.log (bandRoot n : ℝ) ≤ Real.log 4 + Real.log (typedOutputs n : ℝ) := by
  have hM : (0 : ℝ) < typedOutputs n := by exact_mod_cast typedOutputs_pos n
  have hr : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hlo : (typedOutputs n : ℝ) ≤ (bandRoot n : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.le_rootCeiling_sq (typedOutputs n)
  have hup : (bandRoot n : ℝ) ^ 2 ≤ 4 * (typedOutputs n : ℝ) := by
    exact_mod_cast LocalCoverBounds.rootCeiling_sq_le_four (typedOutputs_pos n)
  constructor
  · simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hM hlo
  · simpa only [Real.log_pow, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hM.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (bandRoot n : ℝ) ^ 2) hup

theorem bandRoot_log_rate_sourceProof :
    Tendsto (fun n : ℕ => Real.log (bandRoot n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.E / 5)) := by
  have hl := typedOutputs_log_ratio_tendsto.div_const 2
  have heq : 2 * Parameters.E / 5 / 2 = Parameters.E / 5 := by ring
  rw [heq] at hl
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4 / 2)
  have hu := hl.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).1
    apply (le_div_iff₀ hp).mpr
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2) * Real.log n =
        Real.log (typedOutputs n : ℝ) / 2 := by field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).2
    apply (div_le_iff₀ hp).mpr
    simp only [Pi.inv_apply]
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2 +
        (Real.log 4 / 2) * (Real.log n)⁻¹) * Real.log n =
        (Real.log (typedOutputs n : ℝ) + Real.log 4) / 2 := by field_simp
    rw [he]
    linarith



















































































end

end ThreeSum.BandScales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.BandScales.bandRoot n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      ThreeSum.Parameters.E
      (@OfNat.ofNat.{0} Real (nat_lit 5)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.BandScales.bandRoot_log_rate_sourceProof

#print axioms solution
