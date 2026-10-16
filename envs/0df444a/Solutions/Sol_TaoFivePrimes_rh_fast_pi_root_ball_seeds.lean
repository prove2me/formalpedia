-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_pi_root_ball_seeds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:00:27.944212+00:00
-- url     : https://prove2.me/submissions/0732c942-b8ee-46ec-aeb5-37269636b4a8

import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Mathlib.Analysis.Real.Pi.Bounds
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastPiRootSeedProof
open RHFastBallArithmetic RHFastBallSemantics
noncomputable def D:Nat:=2^128
noncomputable def Q:Nat:=2*10^20
lemma perturb (D:Nat) (a:Ball) (x y:ℂ) (n:Nat)
 (hx:encloses D a x) (hy:‖y-x‖≤(n:ℝ)/(D:ℝ)) : encloses D (inflate a n) y := by
 unfold encloses at hx ⊢
 have h:=norm_sub_le_norm_sub_add_norm_sub y x (value D a)
 apply h.trans
 convert! add_le_add hy hx using 1 <;> simp only [inflate,Nat.cast_add] <;> ring
lemma seed (p:Int) (x:ℝ) (hx:|x-(p:ℝ)/(Q:ℝ)|≤1/(Q:ℝ)) :
 encloses D (inflate (rational D p Q) (D/Q+1)) (x:ℂ) := by
 have hD:0<D:=by norm_num [D]
 have hQ:0<Q:=by norm_num [Q]
 have h:= (TaoFivePrimes.rh_fast_complex_ball_soundness D hD).rational_mem p Q hQ
 apply perturb D _ _ _ _ h
 have he:(x:ℂ)-(p:ℂ)/(Q:ℂ)=((x-(p:ℝ)/(Q:ℝ):ℝ):ℂ):=by push_cast;rfl
 rw [he,Complex.norm_real,Real.norm_eq_abs]
 apply hx.trans
 norm_num [D,Q]
lemma pi_seed : encloses D
 (inflate (rational D 628318530717958647693 Q) (D/Q+1)) (Real.pi:ℂ) := by
 apply seed
 apply abs_le.mpr
 constructor <;> norm_num only [Q,Int.cast_ofNat,Nat.cast_ofNat] <;>
  linarith [Real.pi_gt_d20,Real.pi_lt_d20]
lemma root_seed : encloses D
 (inflate (rational D 501325654926200100483 Q) (D/Q+1)) ((Real.sqrt (2*Real.pi):ℝ):ℂ) := by
 have hlo:(250662827463100050241:ℝ)/10^20≤Real.sqrt (2*Real.pi) :=
  Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d20])
 have hhi:Real.sqrt (2*Real.pi)≤(250662827463100050242:ℝ)/10^20 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [Real.pi_lt_d20]
 apply seed
 apply abs_le.mpr
 constructor <;> norm_num only [Q,Int.cast_ofNat,Nat.cast_ofNat] <;> linarith
end RHFastPiRootSeedProof

theorem solution :
 let D:Nat:=2^128
 let Q:Nat:=2*10^20
 RHFastBallSemantics.encloses D
  (RHFastBallArithmetic.inflate (RHFastBallArithmetic.rational D 628318530717958647693 Q) (D/Q+1)) (Real.pi:ℂ) ∧
 RHFastBallSemantics.encloses D
  (RHFastBallArithmetic.inflate (RHFastBallArithmetic.rational D 501325654926200100483 Q) (D/Q+1))
  ((Real.sqrt (2*Real.pi):ℝ):ℂ) :=
 ⟨RHFastPiRootSeedProof.pi_seed,RHFastPiRootSeedProof.root_seed⟩
#print axioms solution
