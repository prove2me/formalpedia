-- Prove2me | solution 1 for ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:27.641683+00:00
-- url     : https://prove2.me/submissions/9b56e7b8-6602-4bf6-bdef-578068eec9a5

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch

section


/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology






















noncomputable section





















































































































































































































theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < 1 / (5 * Real.log 2) := by positivity
  have h := mu_log_ratio_tendsto.pos_mul_atTop hpos Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn
































































end

end ThreeSum.TrimScales

end

section


/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000









































noncomputable section










































theorem log_mu_add_one_rate :
    Tendsto (fun n : ℕ => Real.log (mu n + 1 : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 1) (by norm_num)).comp TrimScales.mu_tendsto_atTop
  have hh := he.mul mu_log_ratio_tendsto
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hmu : (mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : mu n ≠ 0)
  simp only [Function.comp_def, Nat.cast_one, one_mul]
  field_simp

theorem hierarchyEnvelope_log_rate_sourceProof (C B : ℝ) :
    Tendsto (fun n : ℕ => Real.log (hierarchyEnvelope C B n) / Real.log n) atTop (𝓝 (C / 5)) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2 * C)
  have hid : Real.log 2 * C * (1 / (5 * Real.log 2)) = C / 5 := by field_simp
  rw [hid] at hm
  have hc := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul B
  have hh := log_mu_add_one_rate.add (hm.add hc)
  simp only [mul_zero, add_zero, zero_add] at hh
  convert hh using 1
  funext n
  have hp : (mu n + 1 : ℝ) ≠ 0 := by positivity
  simp only [hierarchyEnvelope, Real.log_mul hp (Real.exp_ne_zero _), Real.log_exp,
    Pi.inv_apply, add_div]
  ring












































































































































































































end
end ThreeSum.HierarchyScales

end


theorem solution : ∀ (C B : Real),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (ThreeSum.HierarchyScales.hierarchyEnvelope C B n))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate_sourceProof

#print axioms solution
