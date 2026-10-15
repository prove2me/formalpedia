-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:21.049386+00:00
-- url     : https://prove2.me/submissions/c662becb-f72b-4bad-8079-af116f6c0809

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
import Theorems.Thm_ThreeSum_BandScales_bandRoot_log_rate


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







theorem mu_multiple_twenty (n : ℕ) : 20 ∣ mu n := by
  unfold mu totalSize blockCount
  exact ⟨(inputBits n / (100 * microSize (inputBits n))) * microSize (inputBits n), by ring⟩































noncomputable section















































theorem mu_div_twenty_real (n : ℕ) : (mu n / 20 : ℕ) = (mu n : ℝ) / 20 := by
  have h := Nat.div_mul_cancel (mu_multiple_twenty n)
  have hr : ((mu n / 20 : ℕ) : ℝ) * 20 = mu n := by exact_mod_cast h
  linarith

theorem bandDivisor_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandDivisor n : ℝ) / Real.log n) atTop (𝓝 (1 / 100)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2 / 20)
  have heq : (Real.log 2 / 20) * (1 / (5 * Real.log 2)) = (1 / 100 : ℝ) := by field_simp; norm_num
  rw [heq] at h
  convert h using 1
  funext n
  simp only [bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mu_div_twenty_real]
  ring

theorem unroundedBand_pos (n : ℕ) : 0 < unroundedBand n := by
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  exact div_pos hR hD

theorem unroundedBand_log_rate :
    Tendsto (fun n : ℕ => Real.log (unroundedBand n) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have h := bandRoot_log_rate.sub bandDivisor_log_rate
  have heq : Parameters.E / 5 - 1 / 100 = (Parameters.E - 1 / 20) / 5 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with n
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  rw [unroundedBand, Real.log_div hR.ne' hD.ne', sub_div]

theorem unroundedBand_eventually_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBand n := by
  have hpos : (0 : ℝ) < (Parameters.E - 1 / 20) / 5 := by have := Parameters.E_bounds.1; linarith
  have hs := unroundedBand_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBand n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBand_pos n).le).mp hb).le

theorem bandSize_ge_unrounded (n : ℕ) : unroundedBand n ≤ (bandSize n : ℝ) := by
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hl : (bandRoot n : ℝ) ≤ (bandDivisor n : ℝ) * bandSize n := by
    exact_mod_cast (bandSize_mul_bounds n).1
  rw [unroundedBand, div_le_iff₀ hD]
  simpa only [mul_comm] using hl

theorem bandSize_eventually_le_twice_unrounded :
    ∀ᶠ n : ℕ in atTop, (bandSize n : ℝ) ≤ 2 * unroundedBand n := by
  filter_upwards [unroundedBand_eventually_ge_one] with n hn
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hu : (bandDivisor n : ℝ) * bandSize n < bandRoot n + bandDivisor n := by
    exact_mod_cast (bandSize_mul_bounds n).2
  have hb : (bandSize n : ℝ) < unroundedBand n + 1 := by
    rw [unroundedBand]
    have heq : ((bandRoot n : ℝ) + bandDivisor n) / bandDivisor n =
        (bandRoot n : ℝ) / bandDivisor n + 1 := by field_simp
    rw [← heq]
    apply (lt_div_iff₀ hD).mpr
    simpa only [mul_comm] using hu
  linarith

theorem bandSize_log_rate_sourceProof :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hu := unroundedBand_log_rate.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBand_log_rate hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBand_pos n) (bandSize_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [bandSize_eventually_le_twice_unrounded, eventually_ge_atTop (1 : ℕ)] with n hn hge
    have hpos : (0 : ℝ) < bandSize n := by exact_mod_cast bandSize_pos n
    have hlog := Real.log_le_log hpos hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (unroundedBand_pos n).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast hge))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd

end

end ThreeSum.BandScales

end


theorem solution : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.BandScales.bandSize n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ThreeSum.Parameters.E
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 20)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))))
      (@OfNat.ofNat.{0} Real (nat_lit 5)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  exact @ThreeSum.BandScales.bandSize_log_rate_sourceProof

#print axioms solution
