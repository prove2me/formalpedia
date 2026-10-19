-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_log_center_seed_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:55:15.030851+00:00
-- url     : https://prove2.me/submissions/4f6ab2a8-ebfd-49ed-b5c9-370f881db851

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Theorems.Thm_TaoFivePrimes_rh_fast_complex_ball_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_center_scalar_seed_soundness
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
namespace RHFastLogCenterSeedProof
open RHFastBallArithmetic RHFastBallSemantics
lemma zero_mem (D:Nat) : encloses D zero (0:ℂ) := by simp [encloses,value,zero]
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


lemma perturb (D:Nat) (a:Ball) (x y:ℂ) (n:Nat)
 (hx:encloses D a x) (hy:‖y-x‖≤(n:ℝ)/(D:ℝ)) : encloses D (inflate a n) y := by
 unfold encloses at hx ⊢
 have h:=norm_sub_le_norm_sub_add_norm_sub y x (value D a)
 apply h.trans
 convert! add_le_add hy hx using 1 <;> simp only [inflate,Nat.cast_add] <;> ring
lemma fold_mem (D:Nat) (hD:0<D) {I:Type*} (is:List I) (f:I→Ball) (g:I→ℂ)
 (h:∀i,encloses D (f i) (g i)) (a:Ball) (z:ℂ) (ha:encloses D a z) :
 encloses D (is.foldl (fun a i=>add a (f i)) a)
  (is.foldl (fun z i=>z+g i) z) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D hD
 induction is generalizing a z with
 | nil=>exact ha
 | cons i is ih=>
  exact ih _ _ (S.add_mem _ _ _ _ ha (h i))
lemma fold_range_sum (n:Nat) (f:Nat→ℂ) (z:ℂ) :
 (List.range n).foldl (fun a i=>a+f i) z=z+∑i∈Finset.range n,f i := by
 induction n with
 | zero=>simp
 | succ n ih=>
  simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,Finset.sum_range_succ]
  ring
lemma fold_range_mem (D:Nat) (hD:0<D) (n:Nat) (f:Nat→Ball) (g:Nat→ℂ)
 (h:∀i,encloses D (f i) (g i)) :
 encloses D ((List.range n).foldl (fun a i=>add a (f i)) zero)
  (∑i∈Finset.range n,g i) := by
 have hs:=fold_mem D hD (List.range n) f g h zero 0 (zero_mem D)
 simpa only [fold_range_sum,zero_add] using hs
local notation "D" => RHFastBallSeedPrograms.D
lemma Dpos : 0<D := by norm_num [RHFastBallSeedPrograms.D]
lemma logSmall_mem (T:Nat) (hlo:2^31 ≤ T) :
 encloses D (RHFastBallSeedPrograms.logSmall T)
   (Complex.log (1+(((-1/(2*(T:ℝ)):ℝ):ℂ)*I))) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 let z:ℂ:=(((-1/(2*(T:ℝ)):ℝ):ℂ)*I)
 have hT0:(0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
 have hTlo:(2147483648:ℝ)≤T := by exact_mod_cast hlo
 have hz:‖z‖≤1/10^9 := by
  simp only [z,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_neg,abs_one,abs_mul,abs_of_pos hT0]
  norm_num only [abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply (div_le_iff₀ (by positivity:0<2*(T:ℝ))).mpr
  linarith
 have hTn:0<T:=by omega
 have h2T:0<2*T:=by omega
 have ha:encloses D (RHFastBallSeedPrograms.small T) z := by
  have h:=S.rotate_mem _ _ 3 (S.rational_mem (-1) (2*T) h2T)
  convert! h using 1 <;> simp only [z,Int.cast_neg,Int.cast_one,Nat.cast_mul,Nat.cast_ofNat]
  norm_num [pow_succ,pow_two]
  push_cast
  ring
 have ht (j:Nat) :
  encloses D (divide (scale (power D (RHFastBallSeedPrograms.small T) (j+1)) ((-1:Int)^(j+2))) (j+1))
   (((-1:ℂ)^(j+2)*z^(j+1))/((j+1:Nat):ℂ)) := by
  have h:=S.divide_mem _ _ (j+1) (by omega)
   (S.scale_mem _ _ ((-1:Int)^(j+2)) (S.power_mem _ _ (j+1) ha))
  simpa only [Int.cast_pow,Int.cast_neg,Int.cast_one] using h
 have hsum:=fold_range_mem D Dpos 4 _ _ ht
 have hid:(∑j∈Finset.range 4,((-1:ℂ)^(j+2)*z^(j+1))/((j+1:Nat):ℂ))=Complex.logTaylor 5 z := by
  norm_num [Complex.logTaylor,Finset.sum_range_succ]
  <;> ring
 rw [hid] at hsum
 have he:=Complex.norm_log_sub_logTaylor_le 4 (show ‖z‖<1 by linarith)
 have hi:(1-‖z‖)⁻¹≤2 := by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith:0<1-‖z‖)).mpr
  linarith
 have hpow:=pow_le_pow_left₀ (norm_nonneg z) hz 5
 have hb:‖Complex.log (1+z)-Complex.logTaylor 5 z‖≤1/(D:ℝ) := by
  apply he.trans
  calc
   _ ≤ ((1/10^9:ℝ)^5*2)/5 := by
    have hm:‖z‖^5*(1-‖z‖)⁻¹≤(1/10^9:ℝ)^5*2 :=
     mul_le_mul hpow hi (inv_nonneg.mpr (by linarith)) (by positivity)
    have hd:=div_le_div_of_nonneg_right hm (show (0:ℝ)≤5 by norm_num)
    convert! hd using 1 <;> norm_num
   _ ≤ _ := by norm_num [RHFastBallSeedPrograms.D]
 have hf:=perturb D _ _ (Complex.log (1+z)) 1 hsum (by simpa only [Nat.cast_one] using hb)
 simpa only [RHFastBallSeedPrograms.logSmall,z] using hf
lemma logCenter_mem (T:Nat) (hlo:2^31 ≤ T) (hhi:T ≤ 2^32) :
 encloses D (RHFastBallSeedPrograms.logCenter T) (Complex.log (RHFastGaussianWindow.center T)) := by
 let S:=TaoFivePrimes.rh_fast_complex_ball_soundness D Dpos
 have hb:encloses D (RHFastBallSeedPrograms.logb T) ((Real.log ((T:ℝ)/2):ℝ):ℂ) :=
  (TaoFivePrimes.rh_fast_center_scalar_seed_soundness T hlo hhi).1
 have hp:encloses D RHFastBallSeedPrograms.pi (Real.pi:ℂ) := TaoFivePrimes.rh_fast_pi_root_ball_seeds.1
 have hi:=S.rotate_mem _ _ 3 (S.divide_mem _ _ 2 (by norm_num) hp)
 have h:=S.add_mem _ _ _ _ (S.add_mem _ _ _ _ hb hi) (logSmall_mem T hlo)
 have hT0:(0:ℝ)<T:=by exact_mod_cast (show 0<T by omega)
 have he:=log_reduction ((T:ℝ)/2) (by positivity)
 have hsmall:small ((T:ℝ)/2)=(((-1/(2*(T:ℝ)):ℝ):ℂ)*I) := by
  unfold small
  congr 1
  push_cast
  ring
 rw [hsmall] at he
 convert! h using 1
 convert! he using 1 <;>
  simp only [RHFastGaussianWindow.center,Complex.ofReal_div,Complex.ofReal_ofNat,Nat.reduceMod]
 <;> norm_num [pow_succ,pow_two]
 <;> ring
end RHFastLogCenterSeedProof

theorem solution (T:Nat) (hlo:2^31 ≤ T) (hhi:T ≤ 2^32) :
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D (RHFastBallSeedPrograms.logCenter T)
  (Complex.log (RHFastGaussianWindow.center T)) := RHFastLogCenterSeedProof.logCenter_mem T hlo hhi
#print axioms solution
