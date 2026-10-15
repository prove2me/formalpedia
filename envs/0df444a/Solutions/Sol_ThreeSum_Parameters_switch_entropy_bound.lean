-- Prove2me | solution 1 for ThreeSum.Parameters.switch_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:53.157513+00:00
-- url     : https://prove2.me/submissions/4cc029ab-9c3a-42bf-bfc6-e1c3718a5c87

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Parameters_entropy_phi_bound


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































































































































































/-! ## Exact rational inequalities for the schedule -/












































































































































































































































/-- The entropy charge including the exact `9/mu` integer-rounding allowance. -/
theorem switch_entropy_bound_sourceProof {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1 / 2))
    (hmu : 0 < mu)
    (hswitch : phi t < switchThreshold a + 9 / ((1 - a) * mu)) :
    (1 - a) * entropy t <
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
  have hden : 0 < 1 - a := by dsimp [terminalFraction] at ha; linarith [ha.2]
  have hr : 0 < entropyRatio := by norm_num [entropyRatio]
  have hh := mul_lt_mul_of_pos_left (entropy_phi_bound ht) hden
  have hp := mul_lt_mul_of_pos_left hswitch (mul_pos hden hr)
  have hid : (1 - a) * entropyRatio *
      (1 + (switchThreshold a + 9 / ((1 - a) * mu))) =
      entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu := by
    unfold switchThreshold
    field_simp [ne_of_gt hden, ne_of_gt hmu]
    ring
  rw [← hid]
  nlinarith


















/-! ## The real-valued ledger, before the algorithmic cost lemmas are applied -/





























































end ThreeSum.Parameters

end
end


theorem solution : ∀ {a t mu : Real},
  @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        ThreeSum.Parameters.terminalFraction)
      a →
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
        t →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) mu →
        @LT.lt.{0} Real Real.instLT (ThreeSum.Parameters.phi t)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (ThreeSum.Parameters.switchThreshold a)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 9)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
                  mu))) →
          @LT.lt.{0} Real Real.instLT
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
              (ThreeSum.Parameters.entropy t))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    ThreeSum.Parameters.boxSaving)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    ThreeSum.Parameters.bandShift)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 9)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  ThreeSum.Parameters.entropyRatio)
                mu)) := by
  exact @ThreeSum.Parameters.switch_entropy_bound_sourceProof

#print axioms solution
