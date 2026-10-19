-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_ball_budget_soundness256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:56:49.259774+00:00
-- url     : https://prove2.me/submissions/5f7af6ed-3593-4536-aa81-3e767ec3bc63

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastBudget256Proof
open RHFastBallArithmetic RHFastBallSemantics RHFastBallFrequencyChecker256
lemma checked (a:Ball) (p:Int×Int) (z:ℂ) (ha:encloses D a z) (hb:budget a p=true) :
 ‖z-((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85‖≤1/(2*10^15:ℝ) := by
 have hD:(0:ℝ)<D:=by norm_num [D]
 let r:Int:=a.re-p.1*(2:Int)^171
 let i:Int:=a.im-p.2*(2:Int)^171
 have he:value D a-((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85=((r:ℂ)+(i:ℂ)*I)/(D:ℂ) := by
  unfold value r i D
  push_cast
  norm_num
  ring
 have hc:‖value D a-((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85‖≤
  ((r.natAbs:ℝ)+(i.natAbs:ℝ))/(D:ℝ) := by
  rw [he,norm_div,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ hD.le
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_I,mul_one,←norm_natAbs r,←norm_natAbs i,Complex.norm_natCast]
  rfl
 have hu:r.natAbs+i.natAbs+a.radius≤D/(2*10^15) := of_decide_eq_true hb
 have hm:(r.natAbs+i.natAbs+a.radius)*(2*10^15)≤D :=
  (Nat.mul_le_mul_right (2*10^15) hu).trans (Nat.div_mul_le_self _ _)
 have hmr:((r.natAbs:ℝ)+(i.natAbs:ℝ)+(a.radius:ℝ))*(2*10^15)≤(D:ℝ) := by exact_mod_cast hm
 have hbound:((r.natAbs:ℝ)+(i.natAbs:ℝ)+(a.radius:ℝ))/(D:ℝ)≤1/(2*10^15:ℝ) := by
  apply (div_le_iff₀ hD).mpr
  nlinarith
 have ht:=norm_sub_le_norm_sub_add_norm_sub z (value D a) (((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85)
 unfold encloses at ha
 apply (ht.trans (add_le_add ha hc)).trans
 convert! hbound using 1 <;> ring
end RHFastBudget256Proof

theorem solution (a:RHFastBallArithmetic.Ball) (p:Int×Int) (z:ℂ)
 (ha:RHFastBallSemantics.encloses RHFastBallFrequencyChecker256.D a z)
 (hb:RHFastBallFrequencyChecker256.budget a p=true) :
 ‖z-((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/(2*10^15:ℝ) := RHFastBudget256Proof.checked a p z ha hb
#print axioms solution
