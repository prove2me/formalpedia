-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_scalar_seed_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:40:30.003527+00:00
-- url     : https://prove2.me/submissions/95aaa4cb-b952-4668-9e04-de44e580d8ac

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_log_ratio_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_pi_root_ball_seeds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastCenterScalarSeedProof
open RHFastBallArithmetic RHFastBallSemantics
local notation "D" => RHFastBallSeedPrograms.D
lemma Dpos : 0<D := by norm_num [RHFastBallSeedPrograms.D]
noncomputable def small (b:ℝ) : ℂ := ((-1/(4*b):ℝ):ℂ)*I
lemma log_reduction (b:ℝ) (hb:0<b) :
 Complex.log (1/4+(b:ℂ)*I)=(Real.log b:ℂ)+((Real.pi/2:ℝ):ℂ)*I+
   Complex.log (1+small b) := by
 have hn:(1+small b).re=1:=by simp only [small,add_re,one_re,mul_re,ofReal_re,ofReal_im,I_re,I_im];ring
 have hi:(1+small b).im<0 := by
  simp only [small,add_im,one_im,mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_one,zero_mul,add_zero,zero_add]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

 have hne:1+small b≠0:=fun h=>by simp [h] at hn
 have ha:=abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr (by rw [hn];norm_num))
 have han:=Complex.arg_neg_iff.mpr hi
 have haI:Complex.arg I+Complex.arg (1+small b)∈Set.Ioc (-Real.pi) Real.pi := by
  rw [Complex.arg_I]
  constructor <;> linarith [Real.pi_pos]
 have hf:1/4+(b:ℂ)*I=(b:ℂ)*(I*(1+small b)) := by
  unfold small
  push_cast
  have hb':(b:ℂ)≠0:=by exact_mod_cast hb.ne'
  field_simp [hb']
  ring_nf
  simp only [I_sq]
  ring
 rw [hf,Complex.log_ofReal_mul hb (mul_ne_zero I_ne_zero hne),Complex.log_mul I_ne_zero hne haI,Complex.log_I]
 push_cast
 ring


lemma logb_mem (T:Nat) (hlo:2^31 ≤ T) (hhi:T ≤ 2^32) :
 encloses D (RHFastBallSeedPrograms.logb T) ((Real.log ((T:ℝ)/2):ℝ):ℂ) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 have h2:=TaoFivePrimes.rh_fast_log_ratio_ball_soundness 2 1 (by norm_num) (by norm_num) (by norm_num)
 have hT:=TaoFivePrimes.rh_fast_log_ratio_ball_soundness T (2^31) (by norm_num) hlo (by omega)
 have h:=S.add_mem _ _ _ _ (S.scale_mem _ _ 30 h2) hT
 have hT0:(0:ℝ)<T:=by exact_mod_cast (show 0<T by omega)
 have hid: Real.log ((T:ℝ)/2)=30*Real.log 2+Real.log ((T:ℝ)/2^31) := by
  rw [Real.log_div hT0.ne' (by norm_num),Real.log_div hT0.ne' (by positivity),Real.log_pow]
  ring
 simpa only [RHFastBallSeedPrograms.logb,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow,div_one,hid,
  Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat,Int.cast_ofNat] using h
lemma omega_mem (T:Nat) (hlo:2^31 ≤ T) (hhi:T ≤ 2^32) :
 encloses D (RHFastBallSeedPrograms.omega T) ((RHFastGaussianWindow.omega T:ℝ):ℂ) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 have hpos:0<T:=by omega
 have hn:0<48*T*T:=by positivity
 have h:=S.sub_mem _ _ _ _ (S.divide_mem _ _ 2 (by norm_num) (logb_mem T hlo hhi))
  (S.rational_mem 1 (48*T*T) hn)
 convert! h using 1
 simp only [RHFastGaussianWindow.omega,Complex.ofReal_sub,Complex.ofReal_div,
  Complex.ofReal_pow,Complex.ofReal_natCast,Nat.cast_mul,Nat.cast_ofNat,Int.cast_one]
 push_cast
 field_simp
 <;> ring
lemma center_mem (T:Nat) : encloses D (RHFastBallSeedPrograms.center T) (RHFastGaussianWindow.center T) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 have h:=S.add_mem _ _ _ _ (S.rational_mem 1 4 (by norm_num))
  (S.rotate_mem _ _ 3 (S.rational_mem (T:Int) 2 (by norm_num)))
 convert! h using 1
 simp only [RHFastGaussianWindow.center,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast,Nat.cast_ofNat,Int.cast_natCast]
 norm_num [pow_succ,pow_two]
 ring
lemma inverse_mem (T:Nat) :
 encloses D (RHFastBallSeedPrograms.inverseCenter T) (RHFastGaussianWindow.center T)⁻¹ := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 have hn:0<1+4*T*T:=by omega
 have h:=S.add_mem _ _ _ _ (S.rational_mem 4 (1+4*T*T) hn)
  (S.rotate_mem _ _ 3 (S.rational_mem (-(8*(T:Int))) (1+4*T*T) hn))
 convert! h using 1
 have hd:(1+4*(T:ℂ)*(T:ℂ))≠0 := by
  norm_cast
  positivity
 have hc:RHFastGaussianWindow.center T≠0 := by
  intro he
  have :=congrArg Complex.re he
  norm_num [RHFastGaussianWindow.center] at this
 apply inv_eq_of_mul_eq_one_right
 simp only [RHFastGaussianWindow.center,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
 norm_num [pow_succ,pow_two]
 have hd':(1+(T:ℂ)^2*4)≠0 := by convert! hd using 1 <;> ring
 field_simp [hd,hd']
 <;> ring_nf
 <;> simp only [I_sq]
 <;> field_simp [hd']
 <;> ring
end RHFastCenterScalarSeedProof

theorem solution (T:Nat) (hlo:2^31 ≤ T) (hhi:T ≤ 2^32) :
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.logb T)
   ((Real.log ((T:ℝ)/2):ℝ):ℂ) ∧
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.omega T)
   ((RHFastGaussianWindow.omega T:ℝ):ℂ) ∧
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.center T)
   (RHFastGaussianWindow.center T) ∧
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.inverseCenter T)
   (RHFastGaussianWindow.center T)⁻¹ :=
 ⟨RHFastCenterScalarSeedProof.logb_mem T hlo hhi,RHFastCenterScalarSeedProof.omega_mem T hlo hhi,
  RHFastCenterScalarSeedProof.center_mem T,RHFastCenterScalarSeedProof.inverse_mem T⟩
#print axioms solution
