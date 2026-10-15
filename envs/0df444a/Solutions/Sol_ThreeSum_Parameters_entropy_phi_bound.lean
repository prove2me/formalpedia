-- Prove2me | solution 1 for ThreeSum.Parameters.entropy_phi_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:26.148527+00:00
-- url     : https://prove2.me/submissions/6bc1855b-65fe-445b-8f9b-1fe9cc010ea3

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Analytic and rational parameter certificate for the proposed 3SUM algorithm

This module certifies the real-variable inequalities and the resulting exponent ledger.
It does not by itself prove that an implementation has those costs: the reduction,
cover, encoding, reporting, arithmetic and machine-model lemmas are separate obligations.

All decimal-looking constants below are exact rational numbers. There are no numerical
oracles, admitted declarations, or native-code decision procedures in this certificate.
-/

noncomputable section

namespace ThreeSum.Parameters

open Set Real

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048







































/-! ## Exact integer witnesses for the logarithmic comparisons -/



theorem power_tangent_left : (100 : ℕ) ^ 100 < 2 ^ 27 * 83 ^ 100 := by norm_num

theorem power_tangent_right :
    (10000 : ℕ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by norm_num










































































































theorem tangentA_bound : tangentA < (27 / 100 : ℝ) := by
  have hp : (100 : ℝ) ^ 100 < 2 ^ 27 * 83 ^ 100 := by
    exact_mod_cast power_tangent_left
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 100 ^ 100) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 27 ≠ 0)
    (by positivity : (83 : ℝ) ^ 100 ≠ 0)] at h
  simp only [Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ log_two_pos).2
  linarith

theorem tangentAB_bound : tangentA + tangentB / 2 < (1413 / 1000 : ℝ) := by
  have hp : (10000 : ℝ) ^ 500 < 2 ^ 1413 * 1411 ^ 500 := by
    exact_mod_cast power_tangent_right
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 10000 ^ 500) hp
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 1413 ≠ 0)
    (by positivity : (1411 : ℝ) ^ 500 ≠ 0)] at h
  simp only [Real.log_pow] at h
  have h10000 : Real.log (10000 : ℝ) = 2 * Real.log 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1411 : Real.log (1411 : ℝ) = Real.log 83 + Real.log 17 := by
    rw [show (1411 : ℝ) = 83 * 17 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [h10000, h1411] at h
  norm_num at h
  have heq : tangentA + tangentB / 2 =
      (Real.log 100 - Real.log 83 / 2 - Real.log 17 / 2) / Real.log 2 := by
    unfold tangentA tangentB
    ring
  rw [heq, div_lt_iff₀ log_two_pos]
  linarith














/-! ## Exact rational inequalities for the schedule -/

























theorem tangent_left_polynomial :
    entropyRatio * (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint)
      = (1691143447 / 6250000000 : ℝ) := by
  norm_num [entropyRatio, tangentPoint, phi, phiDeriv]

theorem tangent_right_polynomial :
    entropyRatio * (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint)
      = (4418702061 / 3125000000 : ℝ) := by
  norm_num [entropyRatio, tangentPoint, phi, phiDeriv]

theorem tangent_left_margin :
    (27 / 100 : ℝ) < entropyRatio *
      (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint) := by
  rw [tangent_left_polynomial]
  norm_num

theorem tangent_right_margin :
    (1413 / 1000 : ℝ) < entropyRatio *
      (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint) := by
  rw [tangent_right_polynomial]
  norm_num

theorem entropy_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    entropy t ≤ tangentA + tangentB * t := by
  have hu : (17 / 100 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hd := Real.hasDerivAt_binEntropy (p := (17 / 100 : ℝ)) (by norm_num) (by norm_num)
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have htan : Real.binEntropy t ≤ Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) := by
    rcases lt_trichotomy t (17 / 100) with h | h | h
    · have hs := hconc.le_slope_of_hasDerivAt ht hu h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
    · subst t
      simp
    · have hs := hconc.slope_le_of_hasDerivAt hu ht h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
  have heq : Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) =
      Real.log 100 - Real.log 83 + t * (Real.log 83 - Real.log 17) := by
    norm_num [Real.binEntropy]
    rw [Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (17 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (83 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (83 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (17 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0)]
    ring
  rw [heq] at htan
  unfold entropy tangentA tangentB
  have hdiv := div_le_div_of_nonneg_right htan log_two_pos.le
  apply le_of_le_of_eq hdiv
  ring

theorem phi_above_tangent {t : ℝ} (ht : 0 ≤ t) :
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by
  have hfact : phi t - (phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) =
      (t - tangentPoint) ^ 2 * (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    unfold phi phiDeriv
    ring
  have hnonneg : 0 ≤ (t - tangentPoint) ^ 2 *
      (18 / 25 + (6 / 25) * (t + 2 * tangentPoint)) := by
    apply mul_nonneg (sq_nonneg _)
    dsimp [tangentPoint]
    linarith
  linarith

/-- A single supporting line gives a uniform bound, including both endpoints. -/
theorem entropy_phi_bound_sourceProof {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    entropy t < entropyRatio * (1 + phi t) := by
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hl := lt_trans tangentA_bound tangent_left_margin
  have hr := lt_trans tangentAB_bound tangent_right_margin
  have hline : tangentA + tangentB * t <
      entropyRatio * (1 + phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) := by
    by_cases hhalf : t < 1 / 2
    · have hp := mul_lt_mul_of_pos_left hl (by linarith : 0 < 1 - 2 * t)
      have hq := mul_le_mul_of_nonneg_left hr.le (by linarith [ht.1] : 0 ≤ 2 * t)
      nlinarith
    · have heq : t = 1 / 2 := by linarith [ht.2]
      rw [heq]
      simpa [div_eq_mul_inv] using hr
  have hpoly := mul_le_mul_of_nonneg_left (phi_above_tangent ht.1)
    (by norm_num [entropyRatio] : 0 ≤ entropyRatio)
  have hent := entropy_tangent ht1
  linarith



































































































































































/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/





























































end ThreeSum.Parameters

end
end


theorem solution : ∀ {t : Real},
  @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      t →
    @LT.lt.{0} Real Real.instLT (ThreeSum.Parameters.entropy t)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (ThreeSum.Parameters.phi t))) := by
  exact @ThreeSum.Parameters.entropy_phi_bound_sourceProof

#print axioms solution
