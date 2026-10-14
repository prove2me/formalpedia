-- Prove2me | solution 1 for TaoFivePrimes.rh_certificate_fastMul_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T09:18:17.146966+00:00
-- url     : https://prove2.me/submissions/30497c8f-5adb-450a-b65e-7d83cc0d66e3

import Definitions.Def_TaoFivePrimes_RHCertificateFastMul
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHScalableArithmeticProof
open RHScalableArithmetic
lemma cross (a0 a1 b0 b1 : Nat) :
    (a0+a1)*(b0+b1)-a0*b0-a1*b1=a0*b1+a1*b0 := by
  have h : (a0+a1)*(b0+b1)=a0*b0+(a1*b1+(a0*b1+a1*b0)) := by ring
  rw [h]
  simp only [Nat.add_sub_cancel_left]
lemma split (a k : Nat) : a-(a >>> k <<< k)+(a >>> k <<< k)=a := by
  rw [Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  exact Nat.sub_add_cancel (Nat.div_mul_le_self a (2^k))
theorem fastMul_correct (n k a b : Nat) : fastMul n k a b=a*b := by
  induction n generalizing k a b with
  | zero => rfl
  | succ n ih =>
    simp only [fastMul,ih]
    rw [cross]
    have ha := split a k
    have hb := split b k
    simp only [Nat.shiftLeft_eq] at ha hb ⊢
    rw [show 2*k=k+k by omega,Nat.pow_add]
    calc
      _ = (a-(a >>> k)*2^k+(a >>> k)*2^k)*(b-(b >>> k)*2^k+(b >>> k)*2^k) := by ring
      _ = a*b := by rw [ha,hb]
end RHScalableArithmeticProof

theorem solution (n k a b : Nat) : RHScalableArithmetic.fastMul n k a b=a*b :=
  RHScalableArithmeticProof.fastMul_correct n k a b
