-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_log_rounded_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:25:32.706438+00:00
-- url     : https://prove2.me/submissions/3b03e48c-7bed-49ee-9783-cec13b47ac84

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelUniformLog
open RHFastKernelHomogeneousHorner RHFastKernelLogData
lemma hom_bound (cs : List Nat) (F x y : Nat) (hxy : 9*x≤y)
    (hc : ∀ c∈cs, c≤F) : 8*hom cs x y*y≤9*F*y^cs.length := by
  induction cs with
  | nil => simp [hom]
  | cons c cs ih =>
    have hhead : c≤F := hc c (by simp)
    have htail : ∀ a∈cs, a≤F := by
      intro a ha
      exact hc a (by simp [ha])
    have ht := ih htail
    simp only [hom,List.length_cons]
    calc
      8*(c*y^cs.length+x*hom cs x y)*y = 8*c*y^(cs.length+1)+x*(8*hom cs x y*y) := by rw [pow_succ];ring
      _ ≤ 8*F*y^(cs.length+1)+x*(9*F*y^cs.length) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hhead)) (Nat.mul_le_mul_left x ht)
      _ = 8*F*y^(cs.length+1)+(9*x)*(F*y^cs.length) := by ring
      _ ≤ 8*F*y^(cs.length+1)+y*(F*y^cs.length) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hxy) _
      _ = 9*F*y^(cs.length+1) := by rw [pow_succ];ring
lemma coefficient_bound : ∀ c∈coefficients, c≤F := by
  have h : coefficients.all (fun c => decide (c≤F))=true := by decide +kernel
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp h c hc)
end RHFastKernelUniformLog

theorem solution (p q scale : Nat) (hp : 3*p≤q) :
    RHFastKernelLogData.rounded p q scale≤scale := by
  open RHFastKernelHomogeneousHorner RHFastKernelLogData in
  have hhom : 8*hom coefficients (p^2) (q^2)*q^2≤9*F*q^80 := by
    have hb := RHFastKernelUniformLog.hom_bound coefficients F (p^2) (q^2)
      (by simpa only [mul_pow, Nat.reducePow] using Nat.pow_le_pow_left hp 2) RHFastKernelUniformLog.coefficient_bound
    change 8*hom coefficients (p^2) (q^2)*q^2≤9*F*(q^2)^40 at hb
    have hpowers : (q^2)^40=q^80 := by ring
    rw [hpowers] at hb
    exact hb
  open RHFastKernelHomogeneousHorner RHFastKernelLogData in
  have hnum : 12*numerator p q≤9*denominator q := by
    unfold numerator denominator
    calc
      12*(2*p*q*hom coefficients (p^2) (q^2)) = 8*q*hom coefficients (p^2) (q^2)*(3*p) := by ring
      _ ≤ 8*q*hom coefficients (p^2) (q^2)*q := Nat.mul_le_mul_left _ hp
      _ = 8*hom coefficients (p^2) (q^2)*q^2 := by ring
      _ ≤ 9*F*q^80 := hhom
      _ = 9*(q^80*F) := by ring
  have hN : RHFastKernelLogData.numerator p q≤RHFastKernelLogData.denominator q := by omega
  unfold RHFastKernelLogData.rounded
  apply Nat.div_le_of_le_mul
  calc
    RHFastKernelLogData.numerator p q*scale≤RHFastKernelLogData.denominator q*scale := Nat.mul_le_mul_right _ hN
    _ = RHFastKernelLogData.denominator q*scale := by ring
#print axioms solution
