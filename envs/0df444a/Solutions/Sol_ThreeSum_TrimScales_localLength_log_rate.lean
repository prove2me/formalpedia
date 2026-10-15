-- Prove2me | solution 1 for ThreeSum.TrimScales.localLength_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:53.82299+00:00
-- url     : https://prove2.me/submissions/257b049f-1710-4442-95e9-752fba167c16

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Theorems.Thm_ThreeSum_TrimScales_localPrime_sq_le_power


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















































































































































theorem localPrime_log2_sq_le (h : ℕ) :
    Nat.log2 (LocalCoverBounds.localPrime h ^ 2) ≤ 4 + 514 * h := by
  rw [Nat.log2_eq_log_two]
  have hm := Nat.log_mono_right (b := 2) (localPrime_sq_le_power h)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hm

theorem localLength_pos (h : ℕ) : 0 < localLength h := by
  simp only [localLength, LocalHashMoments.localSchedule_length]
  positivity

theorem localLength_quadratic_bound (h : ℕ) :
    localLength h ≤ 2 ^ 19 * (h + 1) ^ 2 := by
  have hlog := localPrime_log2_sq_le h
  have hb : localLength h ≤ 320 * (2 * h + 1) * (514 * h + 5) := by
    rw [localLength, LocalHashMoments.localSchedule_length]
    exact Nat.mul_le_mul_left _ (by omega)
  norm_num
  nlinarith [hb]

theorem localLength_log_rate_sourceProof :
    Tendsto (fun h : ℕ => Real.log (localLength h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
  have hlog := BinomialEntropy.logarithmic_error_tendsto_zero (c := 1) (by norm_num)
  have hinv := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hu := (hinv.const_mul (19 / 2 : ℝ)).add (hlog.div_const (Real.log 2))
  simp only [mul_zero, zero_div, zero_add] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun h =>
      div_nonneg (Real.log_natCast_nonneg _) (by positivity))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hlen : (0 : ℝ) < localLength h := by exact_mod_cast localLength_pos h
    have hb : (localLength h : ℝ) ≤ (2 : ℝ) ^ 19 * (h + 1) ^ 2 := by
      exact_mod_cast localLength_quadratic_bound h
    have hlogb := Real.log_le_log hlen hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlogb
    have hd := div_le_div_of_nonneg_right hlogb (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    apply le_of_le_of_eq hd
    simp only [one_mul, Pi.inv_apply, Nat.cast_ofNat]
    field_simp
    ring









































































































end

end ThreeSum.TrimScales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (h : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.TrimScales.localLength h)))
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
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  exact @ThreeSum.TrimScales.localLength_log_rate_sourceProof

#print axioms solution
