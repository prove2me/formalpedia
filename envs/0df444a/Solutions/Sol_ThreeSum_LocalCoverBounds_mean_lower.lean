-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.mean_lower
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:59:49.610567+00:00
-- url     : https://prove2.me/submissions/6cd4779b-db19-4605-acc6-d0c6ff4f5ff0

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators
























































theorem groupSize_lower (h : ℕ) :
    2 ^ (2 * h) ≤ (2 * h + 1) * groupSize h := by
  simpa only [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul,
    groupSize] using Nat.four_pow_le_two_mul_add_one_mul_central_binom h





















































/-- The factor 16 permits a prime above the rounded square-root threshold.
Together with the central-binomial estimate it gives the stated explicit
lower bound on the probability scale. -/
theorem mean_lower_sourceProof {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p)
    (hup : p ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h))) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean L h p := by
  have hM : (0 : ℝ) < outputCount L h := by exact_mod_cast Nat.choose_pos hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hG : (2 : ℝ) ^ (2 * h) ≤ (2 * (h : ℝ) + 1) * groupSize h := by
    exact_mod_cast groupSize_lower h
  have hupper : (p : ℝ) ^ 2 ≤ 16 * ((outputCount L h : ℝ) * 2 ^ (2 * h)) := by
    exact_mod_cast hup
  have hscale := mul_le_mul_of_nonneg_left hG (by positivity :
    (0 : ℝ) ≤ 16 * outputCount L h)
  rw [mean]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end


theorem solution : ∀ {L h p : Nat},
  @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
      L →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
      @LE.le.{0} Nat instLENat
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LocalCoverBounds.outputCount L h)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))) →
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 16)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast h))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
          (ThreeSum.LocalCoverBounds.mean L h p) := by
  exact @ThreeSum.LocalCoverBounds.mean_lower_sourceProof

#print axioms solution
