-- Prove2me | solution 1 for ThreeSum.TrimScales.replicatedHalf_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:59.079421+00:00
-- url     : https://prove2.me/submissions/1a75a09a-d1aa-409e-af16-2126b984e4a1

import Aesop
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Scales
end ThreeSum.Scales

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




theorem replicatedHalf_log_rate_sourceProof {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (a / 5)) := by
  have hl := hf.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : a * (Real.log 2 * (1 / (5 * Real.log 2))) = a / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, replicatedHalf, Nat.cast_pow, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp










































































































































































































































































end

end ThreeSum.TrimScales

end


theorem solution : ∀ {f : Nat → Nat} {a : Real},
  @Filter.Tendsto.{0, 0} Nat Real
      (fun (h : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (Real.log (@Nat.cast.{0} Real Real.instNatCast (f h)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@Nat.cast.{0} Real Real.instNatCast h))
            (Real.log
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        a) →
    @Filter.Tendsto.{0, 0} Nat Real
      (fun (n : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.TrimScales.replicatedHalf f n)))
          (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) a
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.TrimScales.replicatedHalf_log_rate_sourceProof

#print axioms solution
