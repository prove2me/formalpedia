-- Prove2me | solution 1 for ThreeSum.Parameters.phi_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:33.508974+00:00
-- url     : https://prove2.me/submissions/2878be82-3843-4548-9dc8-5d8279b08846

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

theorem power_255 : (2 : ℕ) ^ 799 < 255 ^ 100 := by norm_num










theorem log_255_lower : (799 / 100 : ℝ) * Real.log 2 < Real.log 255 := by
  have hp : (2 : ℝ) ^ 799 < 255 ^ 100 := by exact_mod_cast power_255
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ 799) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith









theorem entropy_eq (t : ℝ) :
    entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [entropy, Real.binEntropy, Real.log_inv]
  ring
































































































































/-! ## Exact rational inequalities for the schedule -/















































































































/-- The two nonnegative initial terms of the convergent logarithm series. -/
theorem neg_log_one_sub_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 ≤ -Real.log (1 - t) := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg ht0 _) (by positivity)) hs
  norm_num [Finset.sum_range_succ] at h
  exact h




theorem gamma_formula {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    gamma t = gammaNumerator t / Real.log 2 := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  unfold gamma
  rw [entropy_eq, entropy_eq]
  rw [show 1 - (1 - t) / 256 = (255 + t) / 256 by ring]
  norm_num
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (255 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h1 (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h255 (by norm_num : (256 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  unfold gammaNumerator
  ring

theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((hasDerivAt_id t).const_mul (799 / 100)).add
    (((hasDerivAt_id t).pow 2).const_mul (18 / 25))).add
      (((hasDerivAt_id t).pow 3).const_mul (6 / 25))
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring























theorem hasDerivAt_gammaNumerator {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    HasDerivAt gammaNumerator (Real.log (255 + t) - Real.log (1 - t)) t := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  have hd1 := (hasDerivAt_id t).const_sub 1
  have hd255 := (hasDerivAt_id t).const_add 255
  have hd := ((hd1.mul (hd1.log h1)).add (hd255.mul (hd255.log h255))).sub_const
    (255 * Real.log 255)
  change HasDerivAt gammaNumerator _ t at hd
  apply hd.congr_deriv
  dsimp only [id_eq]
  field_simp [h1, h255]
  <;> ring

theorem gamma_derivative_above_phi {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    Real.log 2 * phiDeriv t ≤ Real.log (255 + t) - Real.log (1 - t) := by
  have hlog : Real.log 255 ≤ Real.log (255 + t) :=
    Real.log_le_log (by norm_num) (by linarith [ht.1])
  have hneg := neg_log_one_sub_lower ht.1 (by linarith [ht.2])
  have hpoly : 0 ≤ (36 / 25 : ℝ) * t + (18 / 25) * t ^ 2 := by
    nlinarith [ht.1, sq_nonneg t]
  have hprod := mul_le_mul_of_nonneg_right log_two_upper.le hpoly
  dsimp [phiDeriv]
  nlinarith [log_255_lower]

/-- The cubic switch is valid for the entire interval used by every level. -/
theorem phi_le_gamma_sourceProof {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma t := by
  let F : ℝ → ℝ := fun y => gammaNumerator y - Real.log 2 * phi y
  let F' : ℝ → ℝ := fun y =>
    Real.log (255 + y) - Real.log (1 - y) - Real.log 2 * phiDeriv y
  have hd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt F (F' y) y := by
    intro y hy
    exact (hasDerivAt_gammaNumerator hy).sub ((hasDerivAt_phi y).const_mul (Real.log 2))
  have hm : MonotoneOn F (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    exact sub_nonneg.mpr (gamma_derivative_above_phi (interior_subset hy))
  have hmono := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2)) ht ht.1
  have hzero : F 0 = 0 := by norm_num [F, gammaNumerator, phi]
  rw [hzero] at hmono
  rw [gamma_formula ht, le_div_iff₀ log_two_pos]
  dsimp [F] at hmono
  nlinarith
























































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
    @LE.le.{0} Real Real.instLE (ThreeSum.Parameters.phi t) (ThreeSum.Parameters.gamma t) := by
  exact @ThreeSum.Parameters.phi_le_gamma_sourceProof

#print axioms solution
