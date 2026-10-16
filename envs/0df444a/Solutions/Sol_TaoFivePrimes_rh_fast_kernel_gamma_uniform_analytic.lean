-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:09:48.135045+00:00
-- url     : https://prove2.me/submissions/52e2c801-7d1c-4d31-ac49-528f7680fd61

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_base_guards
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_trig_guards
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_exp_guards
import Theorems.Thm_TaoFivePrimes_rh_high_height_complex_stirling
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700
section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHFastKernelScaledApproximation
open Complex
noncomputable def approximant (t : ℝ) : ℂ :=
  let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
  Complex.exp ((z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z))
lemma error_le (t : ℝ) (ht : 2≤t) :
    ‖(Complex.Gamma (1/4+((t/2:ℝ):ℂ)*Complex.I)-approximant t)*
      (Real.exp (Real.pi*t/4):ℂ)‖≤96/t^3 := by
  let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
  have hz : 0<z.re := by norm_num [z]
  have hb : 1≤z.im := by simp [z];linarith
  have he := TaoFivePrimes.rh_high_height_complex_stirling.2 z hz hb
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 (t/2)
  have hg' : ‖Complex.Gamma z‖*Real.exp (Real.pi*t/4)≤6 := by
    convert hg using 1 <;> dsimp [z] <;> congr 1 <;> ring
  have him : z.im=t/2 := by simp [z]
  change ‖(Complex.Gamma z-approximant t)*(Real.exp (Real.pi*t/4):ℂ)‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (2*‖Complex.Gamma z‖/z.im^3)*Real.exp (Real.pi*t/4) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = 2*(‖Complex.Gamma z‖*Real.exp (Real.pi*t/4))/(t/2)^3 := by rw [him];ring
    _ ≤ 2*6/(t/2)^3 := by gcongr
    _ = 96/t^3 := by ring
end RHFastKernelScaledApproximation
end
section

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelHomogeneousHorner
noncomputable def realHorner (cs : List ℝ) (x : ℝ) : ℝ := cs.foldr (fun c p => c+x*p) 0
lemma normalized (cs : List Nat) (x y : Nat) (hy : 0 < y) :
    ((hom cs x y:Nat):ℝ)/(y:ℝ)^cs.length=
      (y:ℝ)⁻¹*realHorner (cs.map (fun c : Nat => (c:ℝ))) ((x:ℝ)/(y:ℝ)) := by
  have hy' : (y:ℝ)≠0 := by exact_mod_cast hy.ne'
  induction cs with
  | nil => simp [hom,realHorner]
  | cons c cs ih =>
    simp only [hom,List.length_cons,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      List.map_cons,realHorner,List.foldr_cons]
    change ((c:ℝ)*(y:ℝ)^cs.length+(x:ℝ)*(hom cs x y:Nat))/(y:ℝ)^(cs.length+1)=_
    calc
      _ = (c:ℝ)/(y:ℝ)+((x:ℝ)/(y:ℝ))*((hom cs x y:Nat)/(y:ℝ)^cs.length) := by
        rw [pow_succ]
        field_simp [hy']
      _ = _ := by rw [ih];unfold realHorner;ring
lemma realHorner_div (cs : List ℝ) (x a : ℝ) :
    realHorner (cs.map (fun c => c/a)) x=realHorner cs x/a := by
  induction cs with
  | nil => simp [realHorner]
  | cons c cs ih =>
    simp only [List.map_cons,realHorner,List.foldr_cons]
    change c/a+x*realHorner (cs.map (fun c => c/a)) x=(c+x*realHorner cs x)/a
    rw [ih]
    ring
end RHFastKernelHomogeneousHorner

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHFastKernelLogApproximation
noncomputable def reduced (u : ℝ) : ℝ := (u-1)/(u+1)
noncomputable def polynomial (x : ℝ) : ℝ :=
  2*∑ i ∈ Finset.range 40, x^(2*i+1)/(2*i+1:ℝ)
lemma reduced_bounds (u : ℝ) (hu : 1≤u ∧ u≤2) :
    0≤reduced u ∧ reduced u≤1/3 := by
  have hp : 0<u+1 := by linarith
  unfold reduced
  constructor
  · exact div_nonneg (by linarith) hp.le
  · apply (div_le_iff₀ hp).mpr
    linarith
lemma reduced_inverse (u : ℝ) (hu : 1≤u) :
    (1+reduced u)/(1-reduced u)=u := by
  have hp : u+1≠0 := by linarith
  unfold reduced
  field_simp
  ring
lemma log40_error (u : ℝ) (hu : 1≤u ∧ u≤2) :
    |Real.log u-polynomial (reduced u)|≤1/10^38 := by
  let x := reduced u
  have hx : 0≤x ∧ x≤1/3 := reduced_bounds u hu
  have hl := Real.sum_range_sub_log_div_le (x:=x)
    (show |x|<1 by rw [abs_of_nonneg hx.1];linarith) 40
  rw [reduced_inverse u hu.1,abs_of_nonneg hx.1] at hl
  have hs : x^2≤1/9 := by nlinarith
  have hxp : x^81≤(1/3:ℝ)^81 := pow_le_pow_left₀ hx.1 hx.2 _
  have hd : 0<1-x^2 := by linarith
  have he : |Real.log u-polynomial x|=
      2*|1/2*Real.log u-∑ i ∈ Finset.range 40, x^(2*i+1)/(2*i+1:ℝ)| := by
    unfold polynomial
    rw [show Real.log u-2*∑ i ∈ Finset.range 40, x^(2*i+1)/(2*i+1:ℝ)=
      2*(1/2*Real.log u-∑ i ∈ Finset.range 40, x^(2*i+1)/(2*i+1:ℝ)) by ring,abs_mul]
    norm_num
  rw [he]
  calc
    _ ≤ 2*(x^81/(1-x^2)) := by norm_num at hl;gcongr
    _ ≤ 2*((1/3:ℝ)^81/(8/9)) := by gcongr <;> linarith
    _ ≤ _ := by norm_num
end RHFastKernelLogApproximation

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFastKernelLogCertificate
open RHFastKernelHomogeneousHorner RHFastKernelLogApproximation
lemma horner_sum (cs : List Nat) (x : ℝ) :
    realHorner (cs.map (fun c : Nat => (c:ℝ))) x=
      ∑ i ∈ Finset.range cs.length, (cs.getD i 0:ℝ)*x^i := by
  induction cs with
  | nil => simp [realHorner]
  | cons c cs ih =>
    simp only [List.map_cons,realHorner,List.foldr_cons,List.length_cons]
    change (c:ℝ)+x*realHorner (cs.map (fun c : Nat => (c:ℝ))) x=_
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero,List.getD_cons_succ,pow_zero,mul_one]
    have hs : (∑ i ∈ Finset.range cs.length, (cs.getD i 0:ℝ)*x^(i+1))=
        x*∑ i ∈ Finset.range cs.length, (cs.getD i 0:ℝ)*x^i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    rw [hs,ih]
    ring
lemma real_polynomial (cs : List Nat) (F : Nat) (hF : 0 < F) (hlen : cs.length=40)
    (hc : ∀ i<40, (2*i+1)*cs.getD i 0=F) (x : ℝ) :
    2*x*(realHorner (cs.map (fun c : Nat => (c:ℝ))) (x^2)/(F:ℝ))=polynomial x := by
  have hF' : (F:ℝ)≠0 := by exact_mod_cast hF.ne'
  rw [horner_sum,hlen,Finset.sum_div,Finset.mul_sum]
  unfold polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hic : i<40 := Finset.mem_range.mp hi
  have he : (2*(i:ℝ)+1)*(cs.getD i 0:ℝ)=(F:ℝ) := by exact_mod_cast hc i hic
  have hk : (2*(i:ℝ)+1)≠0 := by positivity
  have hdiv : (cs.getD i 0:ℝ)/(F:ℝ)=1/(2*(i:ℝ)+1) := by
    apply (div_eq_div_iff hF' hk).mpr
    simpa only [one_mul,mul_one,mul_comm] using he
  calc
    _ = 2*x*((cs.getD i 0:ℝ)/(F:ℝ))*(x^2)^i := by ring
    _ = 2*x*(1/(2*(i:ℝ)+1))*(x^2)^i := by rw [hdiv]
    _ = _ := by rw [←pow_mul,pow_succ];ring
lemma fraction_identity (cs : List Nat) (F p q : Nat) (hF : 0 < F) (hq : 0 < q)
    (hlen : cs.length=40) (hc : ∀ i<40, (2*i+1)*cs.getD i 0=F) :
    ((2*p*q*hom cs (p^2) (q^2):Nat):ℝ)/((q:ℝ)^(2*cs.length)*(F:ℝ))=
      polynomial ((p:ℝ)/(q:ℝ)) := by
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have hF' : (F:ℝ)≠0 := by exact_mod_cast hF.ne'
  have hn := normalized cs (p^2) (q^2) (by positivity : 0 < q^2)
  simp only [Nat.cast_pow,←pow_mul] at hn
  rw [←div_pow] at hn
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ = (2*(p:ℝ)*(q:ℝ)/(F:ℝ))*((hom cs (p^2) (q^2):Nat)/(q:ℝ)^(2*cs.length)) := by ring
    _ = (2*(p:ℝ)*(q:ℝ)/(F:ℝ))*(((q:ℝ)^2)⁻¹*
      realHorner (cs.map (fun c : Nat => (c:ℝ))) (((p:ℝ)/(q:ℝ))^2)) := by rw [hn]
    _ = 2*((p:ℝ)/(q:ℝ))*(realHorner (cs.map (fun c : Nat => (c:ℝ)))
      (((p:ℝ)/(q:ℝ))^2)/(F:ℝ)) := by field_simp [hq',hF']
    _ = _ := real_polynomial cs F hF hlen hc _
end RHFastKernelLogCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelDyadicRounding
lemma nat_division_error (a b : Nat) (hb : 0 < b) :
    |(a:ℝ)/b-((a/b:Nat):ℝ)|≤1 := by
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hr : (0:ℝ)≤(a%b:Nat) := Nat.cast_nonneg _
  have hl : ((a%b:Nat):ℝ)<b := by exact_mod_cast Nat.mod_lt a hb
  have he : ((a/b:Nat):ℝ)*(b:ℝ)+((a%b:Nat):ℝ)=(a:ℝ) := by
    exact_mod_cast Nat.div_add_mod' a b
  have hq : (a:ℝ)/b-((a/b:Nat):ℝ)=((a%b:Nat):ℝ)/b := by
    apply (eq_div_iff hbr.ne').mpr
    field_simp
    linarith
  rw [hq,abs_of_nonneg (div_nonneg hr hbr.le)]
  exact (div_le_one hbr).mpr hl.le
lemma scaled_rounding_error (a b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/b-((a*D/b:Nat):ℝ)/D|≤1/(D:ℝ) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he := nat_division_error (a*D) b hb
  have hq : (a:ℝ)/b-((a*D/b:Nat):ℝ)/D=
      (((a*D:Nat):ℝ)/b-((a*D/b:Nat):ℝ))/D := by
    push_cast
    field_simp
  rw [hq,abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right he hd.le
lemma complex_rounding_error (a c b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    ‖((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*D/b:Nat):ℂ)+((c*D/b:Nat):ℂ)*I)/(D:ℂ)‖≤2/(D:ℝ) := by
  have hr := scaled_rounding_error a b D hb hD
  have hi := scaled_rounding_error c b D hb hD
  have he : ((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*D/b:Nat):ℂ)+((c*D/b:Nat):ℂ)*I)/(D:ℂ)=
      (((a:ℝ)/b-((a*D/b:Nat):ℝ)/D:ℝ):ℂ)+
        (((c:ℝ)/b-((c*D/b:Nat):ℝ)/D:ℝ):ℂ)*I := by push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
end RHFastKernelDyadicRounding

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHFastKernelLogData
open RHFastKernelHomogeneousHorner RHFastKernelLogApproximation RHFastKernelLogCertificate RHFastKernelDyadicRounding
theorem coefficient_check : (List.range 40).all
    (fun i => decide ((2*i+1)*coefficients.getD i 0=F))=true := by decide +kernel
lemma coefficient_identity (i : Nat) (hi : i<40) :
    (2*i+1)*coefficients.getD i 0=F := by
  have h := List.all_eq_true.mp coefficient_check i (List.mem_range.mpr hi)
  exact of_decide_eq_true h
noncomputable def approximation (p q : Nat) : ℝ :=
  ((2*p*q*hom coefficients (p^2) (q^2):Nat):ℝ)/((q:ℝ)^80*(F:ℝ))
lemma approximation_eq (p q : Nat) (hq : 0 < q) :
    approximation p q=polynomial ((p:ℝ)/(q:ℝ)) := by
  simpa only [approximation,show coefficients.length=40 from rfl] using
    fraction_identity coefficients F p q (by decide) hq rfl coefficient_identity
lemma rounded_error (p q D : Nat) (hq : 0 < q) (hD : 0 < D) :
    |approximation p q-(rounded p q D:ℝ)/D|≤1/(D:ℝ) := by
  have hd : 0 < denominator q := by unfold denominator F;positivity
  simpa only [approximation,numerator,denominator,rounded,Nat.cast_mul,Nat.cast_pow] using
    scaled_rounding_error (numerator p q) (denominator q) D hd hD
end RHFastKernelLogData

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelLogData
open RHFastKernelLogApproximation
lemma ratio_bounds (p q : Nat) (hq : 0 < q) (hp : 3*p≤q) :
    1≤((q:ℝ)+p)/((q:ℝ)-p) ∧ ((q:ℝ)+p)/((q:ℝ)-p)≤2 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hp' : 3*(p:ℝ)≤q := by exact_mod_cast hp
  have hpos : 0<(q:ℝ)-p := by nlinarith [Nat.cast_nonneg (α:=ℝ) p]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) p]
  · apply (div_le_iff₀ hpos).mpr
    nlinarith
lemma ratio_reduced (p q : Nat) (hq : 0 < q) (hp : 3*p≤q) :
    reduced (((q:ℝ)+p)/((q:ℝ)-p))=(p:ℝ)/(q:ℝ) := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hp' : 3*(p:ℝ)≤q := by exact_mod_cast hp
  have hd : (q:ℝ)-p≠0 := by nlinarith [Nat.cast_nonneg (α:=ℝ) p]
  have hn : (q:ℝ)+p+(q-p)≠0 := by linarith
  unfold reduced
  field_simp [hq'.ne',hd]
  <;> ring
lemma log_rounded_error (p q D : Nat) (hq : 0 < q) (hD : 0 < D) (hp : 3*p≤q) :
    |Real.log (((q:ℝ)+p)/((q:ℝ)-p))-(rounded p q D:ℝ)/D|≤
      1/(D:ℝ)+1/10^38 := by
  have ha := log40_error (((q:ℝ)+p)/((q:ℝ)-p)) (ratio_bounds p q hq hp)
  rw [ratio_reduced p q hq hp,←approximation_eq p q hq] at ha
  have hr := rounded_error p q D hq hD
  calc
    _ ≤ |Real.log (((q:ℝ)+p)/((q:ℝ)-p))-approximation p q|+
      |approximation p q-(rounded p q D:ℝ)/D| := abs_sub_le _ _ _
    _ ≤ 1/10^38+1/(D:ℝ) := add_le_add ha hr
    _ = _ := by ring
end RHFastKernelLogData

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
namespace RHFastKernelPiSeed
noncomputable def numerator50 : Nat := 314159265358979323846264338327950288419716939937510
lemma seed50 : (numerator50:ℝ)/10^50≤Real.pi ∧
    Real.pi≤(numerator50+1:ℝ)/10^50 := by
  have hp := TaoFivePrimes.rh_pi_enclosure_700
  have hl : (numerator50:ℝ)/10^50≤(TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  have hu : (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700≤(numerator50+1:ℝ)/10^50 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  exact ⟨hl.trans hp.1,hp.2.trans hu⟩
end RHFastKernelPiSeed

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFastKernelLogData
lemma log2_checked : rounded 1 3 D=log2 := by decide +kernel
lemma log2_error : |Real.log 2-(log2:ℝ)/D|≤1/(D:ℝ)+1/10^38 := by
  have h := log_rounded_error 1 3 D (by decide) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat] at h
  rw [log2_checked] at h
  convert h using 1 <;> norm_num
lemma logb_error (bn : Nat) (hbn : 2^36≤bn ∧ bn≤2^37) :
    |Real.log ((bn:ℝ)/64)-
      ((30*log2+rounded (bn-2^36) (bn+2^36) D:Nat):ℝ)/D|≤
        31*(1/(D:ℝ)+1/10^38) := by
  have hD : 0 < D := by decide
  have hq : 0 < bn+2^36 := by omega
  have hp : 3*(bn-2^36)≤bn+2^36 := by omega
  have h := log_rounded_error (bn-2^36) (bn+2^36) D hq hD hp
  have hn : (bn:ℝ)>0 := by exact_mod_cast (show 0 < bn by omega)
  have he : (((bn+2^36:Nat):ℝ)+(bn-2^36:Nat))/
      (((bn+2^36:Nat):ℝ)-(bn-2^36:Nat))=(bn:ℝ)/(2:ℝ)^36 := by
    rw [Nat.cast_sub hbn.1]
    push_cast
    norm_num
    ring
  rw [he] at h
  have hl : Real.log ((bn:ℝ)/64)=30*Real.log 2+Real.log ((bn:ℝ)/(2:ℝ)^36) := by
    rw [Real.log_div hn.ne' (by norm_num : (64:ℝ)≠0),
      Real.log_div hn.ne' (by norm_num : (2:ℝ)^36≠0),Real.log_pow]
    have hs : Real.log (64:ℝ)=6*Real.log 2 := by
      rw [show (64:ℝ)=2^6 by norm_num,Real.log_pow];norm_num
    rw [hs]
    ring
  have herr : Real.log ((bn:ℝ)/64)-
      ((30*log2+rounded (bn-2^36) (bn+2^36) D:Nat):ℝ)/D=
      30*(Real.log 2-(log2:ℝ)/D)+
      (Real.log ((bn:ℝ)/(2:ℝ)^36)-(rounded (bn-2^36) (bn+2^36) D:ℝ)/D) := by
    rw [hl]
    push_cast
    ring
  rw [herr]
  calc
    _ ≤ |30*(Real.log 2-(log2:ℝ)/D)|+
      |Real.log ((bn:ℝ)/(2:ℝ)^36)-(rounded (bn-2^36) (bn+2^36) D:ℝ)/D| := abs_add_le _ _
    _ = 30*|Real.log 2-(log2:ℝ)/D|+
      |Real.log ((bn:ℝ)/(2:ℝ)^36)-(rounded (bn-2^36) (bn+2^36) D:ℝ)/D| := by
        rw [abs_mul];norm_num
    _ ≤ 30*(1/(D:ℝ)+1/10^38)+(1/(D:ℝ)+1/10^38) := by
      exact add_le_add (mul_le_mul_of_nonneg_left log2_error (by norm_num)) h
    _ = _ := by ring
end RHFastKernelLogData

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex CauSeq Finset
namespace RHFastKernelTaylor
lemma exp_factorial_remainder (z : ℂ) (n : Nat) :
    ‖Complex.exp z-∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤
      (‖z‖^n/(n.factorial:ℝ))*Real.exp ‖z‖ := by
  rw [←CauSeq.lim_const (abv:=norm) (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)),
    Complex.exp,sub_eq_add_neg,←CauSeq.lim_neg]
  rw [CauSeq.lim_add (Complex.exp' z) (-CauSeq.const norm (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ))),
    ←Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n,fun j hj => ?_⟩)
  simp_rw [←sub_eq_add_neg]
  change ‖(∑ k ∈ Finset.range j, z^k/(k.factorial:ℂ))-
    ∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤_
  let m := j-n
  have he : j=n+m := (Nat.add_sub_of_le hj).symm
  rw [he,Finset.sum_range_add_sub_sum_range]
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖z^(n+k)/((n+k).factorial:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (‖z‖^n/(n.factorial:ℝ))*(‖z‖^k/(k.factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_div,Complex.norm_pow,norm_natCast,pow_add,norm_mul]
      rw [div_mul_div_comm]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
    _ = (‖z‖^n/(n.factorial:ℝ))*(∑ k ∈ Finset.range m, ‖z‖^k/(k.factorial:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg z) m) (by positivity)
end RHFastKernelTaylor

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHFastKernelGenericExpHorner
open Complex
lemma exp32_error (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖Complex.exp z-∑ k ∈ Finset.range 32, z^k/(k.factorial:ℂ)‖≤1/10^40 := by
  have hp : ‖z‖^32≤(1/2:ℝ)^32 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have he : Real.exp ‖z‖≤3 := le_trans (Real.exp_le_exp.mpr (by linarith)) Real.exp_one_lt_three.le
  calc
    _ ≤ (‖z‖^32/((32).factorial:ℝ))*Real.exp ‖z‖ := RHFastKernelTaylor.exp_factorial_remainder z 32
    _ ≤ ((1/2:ℝ)^32/((32).factorial:ℝ))*3 := mul_le_mul
      (div_le_div_of_nonneg_right hp (by positivity)) he (by positivity) (by positivity)
    _ ≤ _ := by norm_num

lemma cast_horner (cs : List Nat) (x : Nat) :
    ((horner cs x:Nat):ℝ)=(cs.map (fun c : Nat => (c:ℝ))).foldr (fun c p => c+(x:ℝ)*p) 0 := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    change ((c+x*horner cs x:Nat):ℝ)=_
    simp only [Nat.cast_add,Nat.cast_mul,List.map_cons,List.foldr_cons,ih]
lemma polynomial_identity (D d : Nat) (hD : 0<D)
    (hc : d^2*horner (cn D) (d^4)≤horner (cp D) (d^4))
    (hs : d^2*horner (sn D) (d^4)≤horner (sp D) (d^4)) :
    (((horner (cp D) (d^4)-d^2*horner (cn D) (d^4):Nat):ℂ)+
      ((d*(horner (sp D) (d^4)-d^2*horner (sn D) (d^4)):Nat):ℂ)*I)/
        ((D:ℂ)^31*((31).factorial:ℂ))=
    ∑ k ∈ Finset.range 32, (((d:ℂ)/(D:ℂ))*I)^k/(k.factorial:ℂ) := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
  simp only [Nat.cast_sub hc,Nat.cast_sub hs,Nat.cast_mul,Nat.cast_pow]
  simp only [horner,cp,cn,sp,sn,List.foldr_cons,List.foldr_nil,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  simp only [mul_pow,div_pow]
  norm_num [Finset.sum_range_succ,Complex.I_pow_eq_pow_mod,Complex.I_sq]
  field_simp [hd]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three]
  ring
end RHFastKernelGenericExpHorner

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFastKernelNegativeExp
open Complex RHFastKernelGenericExpHorner RHFastKernelDyadicRounding
lemma polynomial_identity (D d : Nat) (hD : 0 < D)
    (hp : d*horner (en D) (d^2)≤horner (ep D) (d^2)) :
    (((horner (ep D) (d^2)-d*horner (en D) (d^2):Nat):ℂ)/
      ((D:ℂ)^31*((31).factorial:ℂ)))=
      ∑ k ∈ Finset.range 32, (-(d:ℂ)/(D:ℂ))^k/(k.factorial:ℂ) := by
  have hd : (D:ℂ)≠0 := by exact_mod_cast hD.ne'
  simp only [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_pow]
  simp only [horner,ep,en,List.foldr_cons,List.foldr_nil,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  norm_num [Finset.sum_range_succ]
  field_simp [hd]
  ring
lemma enclosure (D d : Nat) (hD : 0 < D) (hd : 2*d≤D)
    (hp : d*horner (en D) (d^2)≤horner (ep D) (d^2)) :
    ‖((seed D d:ℂ)/(D:ℂ))-Complex.exp (-(d:ℂ)/(D:ℂ))‖≤
      1/(D:ℝ)+1/10^40 := by
  let p : ℂ := (numerator D d:ℂ)/(denominator D:ℂ)
  have hden : 0 < denominator D := by unfold denominator;positivity
  have hr := scaled_rounding_error (numerator D d) (denominator D) D hden hD
  have hrr : ‖p-(seed D d:ℂ)/(D:ℂ)‖≤1/(D:ℝ) := by
    simpa only [p,seed,←Complex.ofReal_natCast,←Complex.ofReal_div,
      ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hr
  have hi : p=∑ k ∈ Finset.range 32, (-(d:ℂ)/(D:ℂ))^k/(k.factorial:ℂ) := by
    simpa only [p,numerator,denominator,Nat.cast_mul,Nat.cast_pow] using polynomial_identity D d hD hp
  have hz : ‖-(d:ℂ)/(D:ℂ)‖≤1/2 := by
    rw [norm_div,norm_neg,Complex.norm_natCast,Complex.norm_natCast]
    apply (div_le_iff₀ (show (0:ℝ)<D by exact_mod_cast hD)).mpr
    have h : (2:ℝ)*d≤D := by exact_mod_cast hd
    linarith
  have he := exp32_error (-(d:ℂ)/(D:ℂ)) hz
  rw [←hi] at he
  calc
    _ ≤ ‖(seed D d:ℂ)/(D:ℂ)-p‖+‖p-Complex.exp (-(d:ℂ)/(D:ℂ))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add ((norm_sub_rev _ _).trans_le hrr) ((norm_sub_rev _ _).trans_le he)
end RHFastKernelNegativeExp

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelExpEnclosure
open RHFastKernelGenericExpHorner RHFastKernelDyadicRounding
noncomputable def cosNumerator (D d : Nat) : Nat := horner (cp D) (d^4)-d^2*horner (cn D) (d^4)
noncomputable def sinNumerator (D d : Nat) : Nat := d*(horner (sp D) (d^4)-d^2*horner (sn D) (d^4))
noncomputable def denominator (D : Nat) : Nat := D^31*(31).factorial
noncomputable def approximation (D d : Nat) : ℂ :=
  (((cosNumerator D d*D/denominator D:Nat):ℂ)+
    ((sinNumerator D d*D/denominator D:Nat):ℂ)*I)/(D:ℂ)
lemma enclosure (D d : Nat) (hD : 0 < D) (hd : 2*d≤D)
    (hc : d^2*horner (cn D) (d^4)≤horner (cp D) (d^4))
    (hs : d^2*horner (sn D) (d^4)≤horner (sp D) (d^4)) :
    ‖approximation D d-Complex.exp (((d:ℂ)/(D:ℂ))*I)‖≤2/(D:ℝ)+1/10^40 := by
  have hq : 0 < denominator D := by unfold denominator;positivity
  let p : ℂ := ((cosNumerator D d:ℂ)+(sinNumerator D d:ℂ)*I)/(denominator D:ℂ)
  have hp : p=∑ k ∈ Finset.range 32, (((d:ℂ)/(D:ℂ))*I)^k/(k.factorial:ℂ) := by
    simpa only [p,cosNumerator,sinNumerator,denominator,Nat.cast_mul,Nat.cast_pow]
      using polynomial_identity D d hD hc hs
  have hr : ‖p-approximation D d‖≤2/(D:ℝ) :=
    complex_rounding_error (cosNumerator D d) (sinNumerator D d) (denominator D) D hq hD
  have hz : ‖((d:ℂ)/(D:ℂ))*I‖≤1/2 := by
    rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast,Complex.norm_I,mul_one]
    apply (div_le_iff₀ (show (0:ℝ)<D by exact_mod_cast hD)).mpr
    have hd' : (2:ℝ)*d≤D := by exact_mod_cast hd
    linarith
  have he := exp32_error (((d:ℂ)/(D:ℂ))*I) hz
  rw [←hp] at he
  calc
    _ ≤ ‖approximation D d-p‖+‖p-Complex.exp (((d:ℂ)/(D:ℂ))*I)‖ := by
      calc
        _ = ‖(approximation D d-p)+(p-Complex.exp (((d:ℂ)/(D:ℂ))*I))‖ := by congr 1;ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add ((norm_sub_rev (approximation D d) p).trans_le hr)
      ((norm_sub_rev p (Complex.exp (((d:ℂ)/(D:ℂ))*I))).trans_le he)
lemma phase_lipschitz (x y : ℝ) :
    ‖Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))‖≤|x-y| := by
  have he : Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))=
      Complex.exp (I*(y:ℂ))*(Complex.exp (I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp]
  simp only [mul_re,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,sub_self,Real.exp_zero,one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x-y)
lemma power_error (z w : ℂ) (ε : ℝ) (hε : 0≤ε) (hz : ‖z‖≤2)
    (hw : ‖w‖≤1) (he : ‖z-w‖≤ε) (n : Nat) :
    ‖z^n-w^n‖≤((2:ℝ)^n-1)*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwp : ‖w^n‖≤1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hw
    calc
      _ = ‖z*(z^n-w^n)+(z-w)*w^n‖ := by congr 1;ring
      _ ≤ ‖z*(z^n-w^n)‖+‖(z-w)*w^n‖ := norm_add_le _ _
      _ ≤ 2*(((2:ℝ)^n-1)*ε)+ε*1 := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_mul hz ih (norm_nonneg _) (by norm_num))
          (mul_le_mul he hwp (norm_nonneg _) hε)
      _ = _ := by rw [pow_succ];ring
end RHFastKernelExpEnclosure

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelDyadicRounding
lemma int_division_error (a : Int) (b : Nat) (hb : 0 < b) :
    |(a:ℝ)/b-((a/(b:Int):Int):ℝ)|≤1 := by
  have hbi : (0:Int)<b := by exact_mod_cast hb
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hr : (0:ℝ)≤((a%(b:Int):Int):ℝ) := by exact_mod_cast Int.emod_nonneg a hbi.ne'
  have hl : ((a%(b:Int):Int):ℝ)<b := by exact_mod_cast Int.emod_lt_of_pos a hbi
  have he : ((a/(b:Int):Int):ℝ)*(b:ℝ)+((a%(b:Int):Int):ℝ)=(a:ℝ) := by
    exact_mod_cast Int.ediv_mul_add_emod a (b:Int)
  have hq : (a:ℝ)/b-((a/(b:Int):Int):ℝ)=((a%(b:Int):Int):ℝ)/b := by
    apply (eq_div_iff hbr.ne').mpr
    field_simp
    linarith
  rw [hq,abs_of_nonneg (div_nonneg hr hbr.le)]
  exact (div_le_one hbr).mpr hl.le
lemma int_scaled_rounding_error (a : Int) (b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D|≤1/(D:ℝ) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he := int_division_error (a*(D:Int)) b hb
  have hq : (a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D=
      (((a*(D:Int):Int):ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ))/D := by push_cast;field_simp
  rw [hq,abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right he hd.le
lemma int_complex_rounding_error (a c : Int) (b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    ‖((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*(D:Int)/(b:Int):Int):ℂ)+((c*(D:Int)/(b:Int):Int):ℂ)*I)/(D:ℂ)‖≤2/(D:ℝ) := by
  have hr := int_scaled_rounding_error a b D hb hD
  have hi := int_scaled_rounding_error c b D hb hD
  have he : ((a:ℂ)+(c:ℂ)*I)/(b:ℂ)-
      (((a*(D:Int)/(b:Int):Int):ℂ)+((c*(D:Int)/(b:Int):Int):ℂ)*I)/(D:ℂ)=
      (((a:ℝ)/b-((a*(D:Int)/(b:Int):Int):ℝ)/D:ℝ):ℂ)+
        (((c:ℝ)/b-((c*(D:Int)/(b:Int):Int):ℝ)/D:ℝ):ℂ)*I := by push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
end RHFastKernelDyadicRounding

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelGammaArithmetic
noncomputable def value (a : Frac) : ℝ := (a.1:ℝ)/(a.2:ℝ)
lemma value_add (a b : Frac) (ha : 0 < a.2) (hb : 0 < b.2) :
    value (add a b)=value a+value b := by
  have ha' : (a.2:ℝ)≠0 := by exact_mod_cast ha.ne'
  have hb' : (b.2:ℝ)≠0 := by exact_mod_cast hb.ne'
  simp only [value,add,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp
lemma denominator_positive (xs : List Frac) (hx : ∀ a∈xs,0 < a.2) :
    0 < (sum xs).2 := by
  induction xs with
  | nil => simp [sum]
  | cons a xs ih =>
    have ha := hx a (List.mem_cons_self ..)
    have hb := ih (fun b hb => hx b (List.mem_cons_of_mem _ hb))
    exact Nat.mul_pos ha hb
lemma value_sum (xs : List Frac) (hx : ∀ a∈xs,0 < a.2) :
    value (sum xs)=(xs.map value).sum := by
  induction xs with
  | nil => simp [sum,value]
  | cons a xs ih =>
    have ha := hx a (List.mem_cons_self ..)
    have hxs : ∀ b∈xs,0 < b.2 := fun b hb => hx b (List.mem_cons_of_mem _ hb)
    change value (add a (sum xs))=value a+(xs.map value).sum
    rw [value_add a (sum xs) ha (denominator_positive xs hxs),ih hxs]
lemma rounding_error (a : Frac) (ha : 0 < a.2) :
    |value a-(round a:ℝ)/RHFastKernelLogData.D|≤1/(RHFastKernelLogData.D:ℝ) := by
  exact RHFastKernelDyadicRounding.int_scaled_rounding_error a.1 a.2 RHFastKernelLogData.D ha (by decide)
end RHFastKernelGammaArithmetic

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex Set
namespace RHFastKernelStirlingLog
noncomputable def small (b : ℝ) : ℂ := ((-1/(4*b):ℝ):ℂ)*I
lemma small_norm (b : ℝ) (hb : 0 < b) : ‖small b‖=1/(4*b) := by
  rw [small,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  rw [show (-1/(4*b):ℝ)= -(1/(4*b)) by ring,abs_neg,abs_of_pos (by positivity)]
lemma log_reduction (b : ℝ) (hb : 0 < b) :
    Complex.log (1/4+(b:ℂ)*I)=((Real.log b:ℝ):ℂ)+
      ((Real.pi/2:ℝ):ℂ)*I+Complex.log (1+small b) := by
  have hn : (1+small b).re=1 := by
    unfold small
    simp only [add_re,one_re,mul_re,ofReal_re,ofReal_im,I_re,I_im]
    ring
  have hi : (1+small b).im<0 := by
    unfold small
    simp only [add_im,one_im,mul_im,ofReal_re,ofReal_im,I_re,I_im,
      mul_one,zero_mul,add_zero,zero_add]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hne : 1+small b≠0 := by intro h;rw [h] at hn;norm_num at hn
  have ha := abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr (by rw [hn];norm_num))
  have han := Complex.arg_neg_iff.mpr hi
  have haI : Complex.arg I+Complex.arg (1+small b)∈Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I]
    constructor <;> linarith [Real.pi_pos]
  have hf : 1/4+(b:ℂ)*I=(b:ℂ)*(I*(1+small b)) := by
    unfold small
    push_cast
    have hb' : (b:ℂ)≠0 := by exact_mod_cast hb.ne'
    field_simp [hb']
    ring_nf
    simp only [I_sq]
    ring
  rw [hf,Complex.log_ofReal_mul hb (mul_ne_zero I_ne_zero hne),
    Complex.log_mul I_ne_zero hne haI,Complex.log_I]
  push_cast
  ring
noncomputable def approximation (b : ℝ) : ℂ :=
  ((Real.log b:ℝ):ℂ)+((Real.pi/2:ℝ):ℂ)*I+Complex.logTaylor 4 (small b)
lemma log_reduction_error (b : ℝ) (hb : 1500000000≤b) :
    ‖Complex.log (1/4+(b:ℂ)*I)-approximation b‖≤1/10^39 := by
  have hb0 : 0 < b := by linarith
  have hs : ‖small b‖≤1/6000000000 := by
    rw [small_norm b hb0]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hs1 : ‖small b‖<1 := by linarith
  have hg := Complex.norm_log_sub_logTaylor_le 3 hs1
  have hp : ‖small b‖^4≤(1/6000000000:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hs _
  have hi : (1-‖small b‖)⁻¹≤2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1-‖small b‖)).mpr
    linarith
  have he : Complex.log (1/4+(b:ℂ)*I)-approximation b=
      Complex.log (1+small b)-Complex.logTaylor 4 (small b) := by
    rw [log_reduction b hb0]
    unfold approximation
    ring
  rw [he]
  calc
    _ ≤ ‖small b‖^4*(1-‖small b‖)⁻¹/4 := by norm_num at hg;exact hg
    _ ≤ ((1/6000000000:ℝ)^4*2)/4 := by gcongr
    _ ≤ _ := by norm_num
end RHFastKernelStirlingLog

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelStirlingLog
noncomputable def realPart (b t : ℝ) : ℝ :=
  -Real.log b/4+Real.log (2*Real.pi)/2-5/(384*b^2)+
    1/(48*(b^2+1/16))-t^2/800
noncomputable def phasePart (b : ℝ) : ℝ :=
  b*(Real.log b-1)-Real.pi/8+3/(32*b)-1/(768*b^3)-b/(12*(b^2+1/16))
noncomputable def exponent (b t : ℝ) : ℂ :=
  let z : ℂ := 1/4+(b:ℂ)*I
  (z-1/2)*approximation b-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)+
    ((Real.pi*b/2-t^2/800:ℝ):ℂ)
lemma elementary_formula (b t : ℝ) (hb : 0 < b) :
    exponent b t=(realPart b t:ℂ)+(phasePart b:ℂ)*I := by
  have hb' : (b:ℂ)≠0 := by exact_mod_cast hb.ne'
  have hz : (1/4+(b:ℂ)*I:ℂ)≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  have hd : (b:ℂ)^2+1/16≠0 := by
    have hr : (b^2+1/16:ℝ)≠0 := by positivity
    have hc := Complex.ofReal_ne_zero.mpr hr
    push_cast at hc
    exact hc
  have hA : (1+(b:ℂ)*I*4:ℂ)≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  have hB : (1+(b:ℂ)^2*16:ℂ)≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at he
    nlinarith [sq_nonneg b]
  unfold exponent realPart phasePart approximation small Complex.logTaylor
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_pow,one_pow,pow_zero,
    Nat.cast_ofNat,div_zero,mul_zero,zero_mul,add_zero,zero_add,one_mul,mul_one]
  push_cast
  field_simp [hb',hz,hd]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four]
  field_simp [hA,hB]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four]
  ring
end RHFastKernelStirlingLog

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelExpPerturbation
lemma exp_error (z w : ℂ) (h : ‖w-z‖≤1) :
    ‖Complex.exp z-Complex.exp w‖≤2*‖Complex.exp z‖*‖w-z‖ := by
  have he : Complex.exp w-Complex.exp z=
      Complex.exp z*(Complex.exp (w-z)-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 1
    ring
  rw [norm_sub_rev (Complex.exp z) (Complex.exp w),he,norm_mul]
  have hp := mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le h) (norm_nonneg (Complex.exp z))
  convert hp using 1 <;> first | rfl | ring
lemma square_error (a b : ℂ) (ε : ℝ) (hε : 0≤ε ∧ ε≤1)
    (hb : ‖b‖≤1) (he : ‖a-b‖≤ε) : ‖a^2-b^2‖≤3*ε := by
  have ha : ‖a‖≤2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub a b 0
    simp only [sub_zero] at h
    linarith
  calc
    _ = ‖(a-b)*(a+b)‖ := by congr 1;ring
    _ = ‖a-b‖*‖a+b‖ := norm_mul _ _
    _ ≤ ε*(2+1) := mul_le_mul he ((norm_add_le _ _).trans (add_le_add ha hb))
      (norm_nonneg _) hε.1
    _ = _ := by ring
lemma repeated_square_error (a b : ℂ) (ε : ℝ) (hε : 0≤ε) (hb : ‖b‖≤1)
    (he : ‖a-b‖≤ε) (n : Nat) (hn : (3:ℝ)^n*ε≤1) :
    ‖a^(2^n)-b^(2^n)‖≤(3:ℝ)^n*ε := by
  induction n with
  | zero => simpa only [pow_zero,pow_one,one_mul] using he
  | succ n ih =>
    have hp : (3:ℝ)^n*ε≤1 := by
      have hmono : (3:ℝ)^n≤3^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (mul_le_mul_of_nonneg_right hmono hε) hn
    have hi := ih hp
    have hb' : ‖b^(2^n)‖≤1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hb
    have hs := square_error (a^(2^n)) (b^(2^n)) ((3:ℝ)^n*ε) ⟨by positivity,hp⟩ hb' hi
    rw [show (2:Nat)^(n+1)=2^n*2 by rw [pow_succ],pow_mul,pow_mul]
    rw [show (3:ℝ)^(n+1)*ε=3*((3:ℝ)^n*ε) by rw [pow_succ];ring]
    exact hs
end RHFastKernelExpPerturbation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastKernelGammaElementary
open RHFastKernelStirlingLog RHFastKernelExpPerturbation
noncomputable def trueExponent (b t : ℝ) : ℂ :=
  let z : ℂ := 1/4+(b:ℂ)*I
  (z-1/2)*Complex.log z-z+(Real.log (2*Real.pi):ℂ)/2+1/(12*z)+
    ((Real.pi*b/2-t^2/800:ℝ):ℂ)
lemma exponent_error (b t : ℝ) (hb : 1500000000≤b ∧ b≤2000000000) :
    ‖exponent b t-trueExponent b t‖≤3/10^30 := by
  let z : ℂ := 1/4+(b:ℂ)*I
  have he : exponent b t-trueExponent b t=(z-1/2)*(approximation b-Complex.log z) := by
    unfold exponent trueExponent
    dsimp [z]
    ring
  have hn : ‖z-1/2‖≤3000000000 := by
    have hz : z-1/2=((-1/4:ℝ):ℂ)+(b:ℂ)*I := by dsimp [z];push_cast;ring
    rw [hz]
    apply (norm_add_le _ _).trans
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,
      norm_I,mul_one,abs_of_nonneg (by linarith : 0≤b)]
    norm_num
    linarith
  have hl := log_reduction_error b hb.1
  rw [he,norm_mul]
  have hd : ‖approximation b-Complex.log z‖≤1/10^39 := (norm_sub_rev _ _).trans_le hl
  calc
    _ ≤ (3000000000:ℝ)*(1/10^39) := mul_le_mul hn hd (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num
lemma true_exp_factor (b t : ℝ) :
    Complex.exp (trueExponent b t)=RHFastKernelScaledApproximation.approximant (2*b)*
      (Real.exp (Real.pi*b/2):ℂ)*(Real.exp (-t^2/800):ℂ) := by
  unfold trueExponent RHFastKernelScaledApproximation.approximant
  have hz : (((2*b)/2:ℝ):ℂ)=(b:ℂ) := by congr 1;ring
  rw [hz]
  rw [Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma true_exp_norm (b t : ℝ) (hb : 1500000000≤b) :
    ‖Complex.exp (trueExponent b t)‖≤7 := by
  have hb0 : 0 < b := by linarith
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 b
  have hs := RHFastKernelScaledApproximation.error_le (2*b) (by linarith)
  have hs' : ‖(Complex.Gamma (1/4+(b:ℂ)*I)-RHFastKernelScaledApproximation.approximant (2*b))*
      (Real.exp (Real.pi*b/2):ℂ)‖≤1 := by
    have hsmall : (96:ℝ)/(2*b)^3≤1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith [mul_nonneg hb0.le (sq_nonneg b)]
    apply le_trans _ hsmall
    convert hs using 1 <;> congr 4 <;> push_cast <;> ring
  have hΓ : ‖Complex.Gamma (1/4+(b:ℂ)*I)*(Real.exp (Real.pi*b/2):ℂ)‖≤6 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    convert hg using 1 <;> congr 2 <;> ring
  have ha : ‖RHFastKernelScaledApproximation.approximant (2*b)*(Real.exp (Real.pi*b/2):ℂ)‖≤7 := by
    have he : RHFastKernelScaledApproximation.approximant (2*b)*(Real.exp (Real.pi*b/2):ℂ)=
        Complex.Gamma (1/4+(b:ℂ)*I)*(Real.exp (Real.pi*b/2):ℂ)-
          (Complex.Gamma (1/4+(b:ℂ)*I)-RHFastKernelScaledApproximation.approximant (2*b))*
            (Real.exp (Real.pi*b/2):ℂ) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [true_exp_factor,norm_mul]
  have hgauss : ‖(Real.exp (-t^2/800):ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact (mul_le_mul ha hgauss (norm_nonneg _) (by norm_num)).trans_eq (by ring)
end RHFastKernelGammaElementary

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastKernelGammaElementary
open RHFastKernelStirlingLog RHFastKernelExpPerturbation
lemma elementary_gamma_error (b t : ℝ) (hb : 1500000000≤b ∧ b≤2000000000) :
    ‖Complex.Gamma (1/4+(b:ℂ)*I)*
      Complex.exp (((Real.pi*b/2-t^2/800:ℝ):ℂ))-
      Complex.exp ((realPart b t:ℂ)+(phasePart b:ℂ)*I)‖≤1/10^26 := by
  have hb0 : 0 < b := by linarith
  let f : ℂ := Complex.Gamma (1/4+(b:ℂ)*I)*
      Complex.exp (((Real.pi*b/2-t^2/800:ℝ):ℂ))
  have hst : ‖(Complex.Gamma (1/4+(b:ℂ)*I)-RHFastKernelScaledApproximation.approximant (2*b))*
      (Real.exp (Real.pi*b/2):ℂ)‖≤4/10^27 := by
    have h := RHFastKernelScaledApproximation.error_le (2*b) (by linarith)
    have hs : (96:ℝ)/(2*b)^3≤4/10^27 := by
      calc
        _ ≤ 96/(3000000000:ℝ)^3 := by gcongr;linarith
        _ ≤ _ := by norm_num
    apply le_trans _ hs
    convert h using 1 <;> congr 4 <;> push_cast <;> ring
  have hgauss : ‖(Real.exp (-t^2/800):ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hfactor : Complex.exp (((Real.pi*b/2-t^2/800:ℝ):ℂ))=
      (Real.exp (Real.pi*b/2):ℂ)*(Real.exp (-t^2/800):ℂ) := by
    rw [Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfirst : ‖f-Complex.exp (trueExponent b t)‖≤4/10^27 := by
    have he : f-Complex.exp (trueExponent b t)=
        ((Complex.Gamma (1/4+(b:ℂ)*I)-RHFastKernelScaledApproximation.approximant (2*b))*
          (Real.exp (Real.pi*b/2):ℂ))*(Real.exp (-t^2/800):ℂ) := by
      dsimp [f]
      rw [hfactor,true_exp_factor]
      ring
    rw [he,norm_mul]
    exact (mul_le_mul hst hgauss (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hd := exponent_error b t hb
  have hp := exp_error (trueExponent b t) (exponent b t) (hd.trans (by norm_num))
  have hsecond : ‖Complex.exp (trueExponent b t)-Complex.exp (exponent b t)‖≤42/10^30 := by
    apply hp.trans
    calc
      _ ≤ (2:ℝ)*7*(3/10^30) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (true_exp_norm b t hb.1) (by norm_num))
          hd (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  rw [←elementary_formula b t hb0]
  calc
    _ ≤ ‖f-Complex.exp (trueExponent b t)‖+
        ‖Complex.exp (trueExponent b t)-Complex.exp (exponent b t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4/10^27+42/10^30 := add_le_add hfirst hsecond
    _ ≤ _ := by norm_num
end RHFastKernelGammaElementary

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelLogData
lemma log_order_error (x y : ℝ) (hx : 1≤x) (hxy : x≤y) :
    0≤Real.log y-Real.log x ∧ Real.log y-Real.log x≤y-x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hx0 hxy)
  · rw [←Real.log_div hy0.ne' hx0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    have he : y/x-1=(y-x)/x := by field_simp
    rw [he] at h
    exact h.trans (div_le_self (sub_nonneg.mpr hxy) hx)
lemma log_lipschitz (x y : ℝ) (hx : 1≤x) (hy : 1≤y) :
    |Real.log x-Real.log y|≤|x-y| := by
  rcases le_total x y with hxy|hyx
  · have h := log_order_error x y hx hxy
    rw [abs_sub_comm (Real.log x),abs_of_nonneg h.1,abs_sub_comm x,abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h.2
  · have h := log_order_error y x hy hyx
    rw [abs_of_nonneg h.1,abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h.2
lemma log2pi_checked : 2*log2+rounded
    (RHFastKernelPiSeed.numerator50-2*10^50) (RHFastKernelPiSeed.numerator50+2*10^50) D=log2pi := by decide +kernel
lemma log2pi_error : |Real.log (2*Real.pi)-(log2pi:ℝ)/D|≤
    3*(1/(D:ℝ)+1/10^38)+1/10^50 := by
  let P : Nat := RHFastKernelPiSeed.numerator50
  have hp : 3*10^50≤P ∧ P≤4*10^50 := by decide
  have hq : 0 < P+2*10^50 := by omega
  have hred : 3*(P-2*10^50)≤P+2*10^50 := by omega
  have h := log_rounded_error (P-2*10^50) (P+2*10^50) D hq (by decide) hred
  have he : (((P+2*10^50:Nat):ℝ)+(P-2*10^50:Nat))/
      (((P+2*10^50:Nat):ℝ)-(P-2*10^50:Nat))=(P:ℝ)/(2*10^50) := by
    rw [Nat.cast_sub (show 2*10^50≤P by omega)]
    push_cast
    norm_num
    ring
  rw [he] at h
  have hb : (P:ℝ)/10^50≤Real.pi ∧ Real.pi≤(P+1:ℝ)/10^50 := RHFastKernelPiSeed.seed50
  have hpn : (3:ℝ)*10^50≤P := by exact_mod_cast hp.1
  have hL : |Real.log (Real.pi/2)-Real.log ((P:ℝ)/(2*10^50))|≤1/10^50 := by
    have hl := log_lipschitz (Real.pi/2) ((P:ℝ)/(2*10^50))
      (by linarith [Real.pi_gt_three]) (by apply (le_div_iff₀ (by norm_num : (0:ℝ)<2*10^50)).mpr;linarith)
    apply hl.trans
    rw [abs_of_nonneg (by linarith [hb.1] : 0≤Real.pi/2-(P:ℝ)/(2*10^50))]
    linarith [hb.2]
  have hl : Real.log (2*Real.pi)=2*Real.log 2+Real.log (Real.pi/2) := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_pos.ne',
      Real.log_div Real.pi_pos.ne' (by norm_num : (2:ℝ)≠0)]
    ring
  have hident : (log2pi:ℝ)/D=(2:ℝ)*(log2:ℝ)/D+
      (rounded (P-2*10^50) (P+2*10^50) D:ℝ)/D := by
    dsimp only [P]
    rw [←log2pi_checked]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [hl,hident]
  have herr : 2*Real.log 2+Real.log (Real.pi/2)-
      (2*(log2:ℝ)/D+(rounded (P-2*10^50) (P+2*10^50) D:ℝ)/D)=
      2*(Real.log 2-(log2:ℝ)/D)+
      (Real.log (Real.pi/2)-Real.log ((P:ℝ)/(2*10^50)))+
      (Real.log ((P:ℝ)/(2*10^50))-(rounded (P-2*10^50) (P+2*10^50) D:ℝ)/D) := by ring
  rw [herr]
  have h2 : |2*(Real.log 2-(log2:ℝ)/D)|≤2*(1/(D:ℝ)+1/10^38) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left log2_error (by norm_num)
  calc
    _ ≤ |2*(Real.log 2-(log2:ℝ)/D)+
        (Real.log (Real.pi/2)-Real.log ((P:ℝ)/(2*10^50)))|+
      |Real.log ((P:ℝ)/(2*10^50))-(rounded (P-2*10^50) (P+2*10^50) D:ℝ)/D| := abs_add_le _ _
    _ ≤ (2*(1/(D:ℝ)+1/10^38)+1/10^50)+(1/(D:ℝ)+1/10^38) :=
      add_le_add ((abs_add_le _ _).trans (add_le_add h2 hL)) h
    _ = _ := by ring
end RHFastKernelLogData

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaDyadic
open RHFastKernelStirlingLog RHFastKernelGammaElementary RHFastKernelExpPerturbation
noncomputable def realFormula (b t L C : ℝ) : ℝ :=
  -L/4+C/2-5/(384*b^2)+1/(48*(b^2+1/16))-t^2/800
noncomputable def phaseFormula (b L p : ℝ) : ℝ :=
  b*(L-1)-p/8+3/(32*b)-1/(768*b^3)-b/(12*(b^2+1/16))
lemma realFormula_error (b t L C : ℝ) (hL : |Real.log b-L|≤1/10^36)
    (hC : |Real.log (2*Real.pi)-C|≤1/10^37) :
    |RHFastKernelStirlingLog.realPart b t-realFormula b t L C|≤1/10^36 := by
  have he : RHFastKernelStirlingLog.realPart b t-realFormula b t L C=
      -(Real.log b-L)/4+(Real.log (2*Real.pi)-C)/2 := by
    unfold RHFastKernelStirlingLog.realPart realFormula;ring
  rw [he]
  calc
    _ ≤ |-(Real.log b-L)/4|+|(Real.log (2*Real.pi)-C)/2| := abs_add_le _ _
    _ = |Real.log b-L|/4+|Real.log (2*Real.pi)-C|/2 := by simp only [abs_div,abs_neg];norm_num
    _ ≤ (1/10^36)/4+(1/10^37)/2 := by gcongr
    _ ≤ _ := by norm_num
lemma phaseFormula_error (b L p : ℝ) (hb : 1500000000≤b ∧ b≤2000000000)
    (hL : |Real.log b-L|≤1/10^36) (hp : |Real.pi-p|≤1/10^50) :
    |phasePart b-phaseFormula b L p|≤3/10^27 := by
  have he : phasePart b-phaseFormula b L p=b*(Real.log b-L)-(Real.pi-p)/8 := by
    unfold phasePart phaseFormula;ring
  rw [he]
  calc
    _ ≤ |b*(Real.log b-L)|+|(Real.pi-p)/8| := abs_sub _ _
    _ = b*|Real.log b-L|+|Real.pi-p|/8 := by
      rw [abs_mul,abs_of_nonneg (by linarith : 0≤b),abs_div];norm_num
    _ ≤ (2000000000:ℝ)*(1/10^36)+(1/10^50)/8 := by gcongr <;> exact hb.2
    _ ≤ _ := by norm_num
lemma elementary_exp_norm (b t : ℝ) (hb : 1500000000≤b ∧ b≤2000000000) :
    ‖Complex.exp ((RHFastKernelStirlingLog.realPart b t:ℂ)+(phasePart b:ℂ)*I)‖≤8 := by
  have he := exponent_error b t hb
  have hp := exp_error (trueExponent b t) (exponent b t) (he.trans (by norm_num))
  have hn := true_exp_norm b t hb.1
  have hdiff : ‖Complex.exp (trueExponent b t)-Complex.exp (exponent b t)‖≤42/10^30 := by
    apply hp.trans
    calc
      _ ≤ (2:ℝ)*7*(3/10^30) := mul_le_mul
        (mul_le_mul_of_nonneg_left hn (by norm_num)) he (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  rw [←elementary_formula b t (by linarith)]
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (Complex.exp (exponent b t))
    (Complex.exp (trueExponent b t)) 0
  simp only [sub_zero,norm_sub_rev (Complex.exp (exponent b t)) (Complex.exp (trueExponent b t))] at htriangle
  linarith
lemma rounded_exponent_error (b t L C p rr ii : ℝ)
    (hb : 1500000000≤b ∧ b≤2000000000)
    (hL : |Real.log b-L|≤1/10^36) (hC : |Real.log (2*Real.pi)-C|≤1/10^37)
    (hp : |Real.pi-p|≤1/10^50)
    (hr : |realFormula b t L C-rr|≤1/10^38)
    (hi : |phaseFormula b L p-ii|≤1/10^38) :
    ‖((rr:ℂ)+(ii:ℂ)*I)-((RHFastKernelStirlingLog.realPart b t:ℂ)+(phasePart b:ℂ)*I)‖≤4/10^27 := by
  have hR := (abs_sub_le (RHFastKernelStirlingLog.realPart b t) (realFormula b t L C) rr).trans
    (add_le_add (realFormula_error b t L C hL hC) hr)
  have hI := (abs_sub_le (phasePart b) (phaseFormula b L p) ii).trans
    (add_le_add (phaseFormula_error b L p hb hL hp) hi)
  have he : ((rr:ℂ)+(ii:ℂ)*I)-((RHFastKernelStirlingLog.realPart b t:ℂ)+(phasePart b:ℂ)*I)=
      ((rr-RHFastKernelStirlingLog.realPart b t:ℝ):ℂ)+((ii-phasePart b:ℝ):ℂ)*I := by push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,abs_sub_comm rr,abs_sub_comm ii]
  linarith
lemma gamma_rounded_exp_error (b t L C p rr ii : ℝ)
    (hb : 1500000000≤b ∧ b≤2000000000)
    (hL : |Real.log b-L|≤1/10^36) (hC : |Real.log (2*Real.pi)-C|≤1/10^37)
    (hp : |Real.pi-p|≤1/10^50)
    (hr : |realFormula b t L C-rr|≤1/10^38)
    (hi : |phaseFormula b L p-ii|≤1/10^38) :
    ‖Complex.Gamma (1/4+(b:ℂ)*I)*Complex.exp (((Real.pi*b/2-t^2/800:ℝ):ℂ))-
      Complex.exp ((rr:ℂ)+(ii:ℂ)*I)‖≤8/10^26 := by
  have hd := rounded_exponent_error b t L C p rr ii hb hL hC hp hr hi
  have he := exp_error ((RHFastKernelStirlingLog.realPart b t:ℂ)+(phasePart b:ℂ)*I) ((rr:ℂ)+(ii:ℂ)*I)
    (hd.trans (by norm_num))
  have hexp : ‖Complex.exp ((RHFastKernelStirlingLog.realPart b t:ℂ)+(phasePart b:ℂ)*I)-
      Complex.exp ((rr:ℂ)+(ii:ℂ)*I)‖≤64/10^27 := by
    apply he.trans
    calc
      _ ≤ (2:ℝ)*8*(4/10^27) := mul_le_mul
        (mul_le_mul_of_nonneg_left (elementary_exp_norm b t hb) (by norm_num)) hd (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (elementary_gamma_error b t hb) hexp)).trans (by norm_num)
end RHFastKernelGammaDyadic

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFastKernelGammaArithmetic
open RHFastKernelLogData RHFastKernelGammaDyadic
noncomputable def realInput (bn : Nat) (n lb : Int) : Frac :=
  sum [(-lb+2*(log2pi:Int),4*D),(-160,3*bn^2),
    (256,3*(bn^2+256)),(-n*n,819200)]
noncomputable def phaseInput (bn : Nat) (lb : Int) : Frac :=
  sum [((bn:Int)*(lb-(D:Int)),64*D),(-(P:Int),8*10^50),
    (6,bn),(-1024,3*bn^3),(-16*(bn:Int),3*(bn^2+256))]
lemma realInput_positive (bn : Nat) (n lb : Int) (hb : 0 < bn) : 0 < (realInput bn n lb).2 := by
  apply denominator_positive
  simp only [List.forall_mem_cons,List.forall_mem_nil,Prod.snd]
  exact ⟨by unfold D;positivity,by positivity,by positivity,by norm_num,by simp⟩
lemma phaseInput_positive (bn : Nat) (lb : Int) (hb : 0 < bn) : 0 < (phaseInput bn lb).2 := by
  apply denominator_positive
  simp only [List.forall_mem_cons,List.forall_mem_nil,Prod.snd]
  exact ⟨by unfold D;positivity,by norm_num,hb,by positivity,by positivity,by simp⟩
lemma realInput_value (bn : Nat) (n lb : Int) (hb : 0 < bn) :
    value (realInput bn n lb)=realFormula ((bn:ℝ)/64) ((n:ℝ)/32)
      ((lb:ℝ)/D) ((log2pi:ℝ)/D) := by
  have hb' : (bn:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hD : (D:ℝ)≠0 := by norm_num [D]
  unfold realInput
  rw [value_sum]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,value,
      Prod.fst,Prod.snd,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_natCast,Int.cast_ofNat,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    unfold realFormula
    field_simp [hb',hD]
    ring
  · simp only [List.forall_mem_cons,List.forall_mem_nil,Prod.snd]
    exact ⟨by unfold D;positivity,by positivity,by positivity,by norm_num,by simp⟩
lemma phaseInput_value (bn : Nat) (lb : Int) (hb : 0 < bn) :
    value (phaseInput bn lb)=phaseFormula ((bn:ℝ)/64) ((lb:ℝ)/D) ((P:ℝ)/10^50) := by
  have hb' : (bn:ℝ)≠0 := by exact_mod_cast hb.ne'
  have hD : (D:ℝ)≠0 := by norm_num [D]
  unfold phaseInput
  rw [value_sum]
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,value,
      Prod.fst,Prod.snd,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_neg,Int.cast_natCast,Int.cast_ofNat,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    unfold phaseFormula
    field_simp [hb',hD]
    ring
  · simp only [List.forall_mem_cons,List.forall_mem_nil,Prod.snd]
    exact ⟨by unfold D;positivity,by norm_num,hb,by positivity,by positivity,by simp⟩
end RHFastKernelGammaArithmetic

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaArithmetic
open RHFastKernelLogData RHFastKernelGammaDyadic
noncomputable def logInput (bn : Nat) : Int :=
  30*(RHFastKernelLogData.log2:Int)+(rounded (bn-2^36) (bn+2^36) D:Int)
lemma logInput_error (bn : Nat) (hbn : 2^36≤bn ∧ bn≤2^37) :
    |Real.log ((bn:ℝ)/64)-(logInput bn:ℝ)/D|≤1/10^36 := by
  have h := RHFastKernelLogData.logb_error bn hbn
  have he : (logInput bn:ℝ)=((30*RHFastKernelLogData.log2+
      rounded (bn-2^36) (bn+2^36) D:Nat):ℝ) := by
    simp only [logInput,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [he]
  exact h.trans (by norm_num [D])
lemma logPiInput_error : |Real.log (2*Real.pi)-(log2pi:ℝ)/D|≤1/10^37 := by
  exact RHFastKernelLogData.log2pi_error.trans (by norm_num [D])
lemma piInput_error : |Real.pi-(P:ℝ)/10^50|≤1/10^50 := by
  have h := RHFastKernelPiSeed.seed50
  change |Real.pi-(RHFastKernelPiSeed.numerator50:ℝ)/10^50|≤1/10^50
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  change Real.pi-(RHFastKernelPiSeed.numerator50:ℝ)/10^50≤_
  linarith [h.2]
lemma gamma_input_error (bn : Nat) (n : Int)
    (hbn : 96000000000≤bn ∧ bn≤128000000000) :
    ‖Complex.Gamma (1/4+((bn:ℂ)/64)*I)*
      Complex.exp (((Real.pi*((bn:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ))-
      Complex.exp ((round (realInput bn n (logInput bn)):ℂ)/(D:ℂ)+
        ((round (phaseInput bn (logInput bn)):ℂ)/(D:ℂ))*I)‖≤8/10^26 := by
  have hb0 : 0 < bn := by omega
  have hb : 1500000000≤(bn:ℝ)/64 ∧ (bn:ℝ)/64≤2000000000 := by
    have hl : (96000000000:ℝ)≤bn := by exact_mod_cast hbn.1
    have hu : (bn:ℝ)≤128000000000 := by exact_mod_cast hbn.2
    constructor <;> linarith
  have hlog : 2^36≤bn ∧ bn≤2^37 := by omega
  have hr := rounding_error (realInput bn n (logInput bn)) (realInput_positive bn n _ hb0)
  have hi := rounding_error (phaseInput bn (logInput bn)) (phaseInput_positive bn _ hb0)
  rw [realInput_value bn n _ hb0] at hr
  rw [phaseInput_value bn _ hb0] at hi
  have hr' := hr.trans (by norm_num [D] : 1/(D:ℝ)≤1/10^38)
  have hi' := hi.trans (by norm_num [D] : 1/(D:ℝ)≤1/10^38)
  have h := gamma_rounded_exp_error ((bn:ℝ)/64) ((n:ℝ)/32)
    ((logInput bn:ℝ)/D) ((log2pi:ℝ)/D) ((P:ℝ)/10^50)
    ((round (realInput bn n (logInput bn)):ℝ)/D)
    ((round (phaseInput bn (logInput bn)):ℝ)/D) hb
    (logInput_error bn hlog) logPiInput_error piInput_error hr' hi'
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_intCast,
    Complex.ofReal_ofNat] using h
end RHFastKernelGammaArithmetic

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaPhase
open RHFastKernelExpEnclosure
lemma periodic (y : ℝ) (k : Int) :
    Complex.exp (I*((y+2*Real.pi*(k:ℝ):ℝ):ℂ))=Complex.exp (I*(y:ℂ)) := by
  have he : I*((y+2*Real.pi*(k:ℝ):ℝ):ℂ)=
      I*(y:ℂ)+(k:ℂ)*(2*(Real.pi:ℂ)*I) := by push_cast;ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
lemma reduction_error (x y p : ℝ) (k : Int) (D : Nat) (hD : 0 < D)
    (hp : |p-Real.pi|≤1/10^50) (hk : |(k:ℝ)|≤10000000000)
    (hxy : |x-2*p*(k:ℝ)-y|≤8/(D:ℝ)) :
    ‖Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))‖≤8/(D:ℝ)+2/10^40 := by
  have hl := phase_lipschitz x (y+2*Real.pi*(k:ℝ))
  rw [periodic y k] at hl
  apply hl.trans
  have he : x-(y+2*Real.pi*(k:ℝ))=
      (x-2*p*(k:ℝ)-y)+2*(p-Real.pi)*(k:ℝ) := by ring
  rw [he]
  calc
    _ ≤ |x-2*p*(k:ℝ)-y|+|2*(p-Real.pi)*(k:ℝ)| := abs_add_le _ _
    _ = |x-2*p*(k:ℝ)-y|+2*|p-Real.pi| *|(k:ℝ)| := by rw [abs_mul,abs_mul];norm_num
    _ ≤ 8/(D:ℝ)+2*(1/10^50)*10000000000 := by gcongr
    _ = _ := by norm_num
lemma power8_error (a : ℂ) (y : ℝ) (ha : ‖a-Complex.exp (I*(y:ℂ))‖≤1/10^37) :
    ‖a^8-Complex.exp (I*((8*y:ℝ):ℂ))‖≤255/10^37 := by
  have hw : ‖Complex.exp (I*(y:ℂ))‖=1 := by
    simpa only [mul_comm] using Complex.norm_exp_I_mul_ofReal y
  have hn : ‖a‖≤2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub a (Complex.exp (I*(y:ℂ))) 0
    simp only [sub_zero,hw] at ht
    linarith
  have h := power_error a (Complex.exp (I*(y:ℂ))) (1/10^37) (by positivity) hn hw.le ha 8
  have he : Complex.exp (I*(y:ℂ))^8=Complex.exp (I*((8*y:ℝ):ℂ)) := by
    rw [←Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at h
  norm_num at h ⊢
  exact h
end RHFastKernelGammaPhase

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelChirpSeed
open RHFastKernelPiSeed RHFastKernelDyadicRounding RHFastKernelExpEnclosure RHFastKernelGenericExpHorner
noncomputable def point (N q D : Nat) : Nat := numerator50*q*D/(8*N*10^50)
lemma quantization_error (N q D : Nat) (hN : 0 < N) (hD : 0 < D) (hq : q≤N) :
    |Real.pi*(q:ℝ)/(8*(N:ℝ))-(point N q D:ℝ)/D|≤1/(D:ℝ)+1/10^50 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hqr : (q:ℝ)≤N := by exact_mod_cast hq
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hv : (q:ℝ)/(8*N)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hs : |Real.pi-(numerator50:ℝ)/10^50|≤1/10^50 := by
    rw [abs_of_nonneg (by linarith [seed50.1])]
    linarith [seed50.2]
  have hp : |Real.pi*(q:ℝ)/(8*N)-(numerator50*q:Nat)/(8*N*10^50:Nat)|≤1/10^50 := by
    have he : Real.pi*(q:ℝ)/(8*N)-(numerator50*q:Nat)/(8*N*10^50:Nat)=
        (Real.pi-(numerator50:ℝ)/10^50)*((q:ℝ)/(8*N)) := by push_cast;ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(q:ℝ)/(8*N))]
    exact (mul_le_mul hs hv (by positivity) (by positivity)).trans_eq (by ring)
  have hr := scaled_rounding_error (numerator50*q) (8*N*10^50) D (by positivity) hD
  change |((numerator50*q:Nat):ℝ)/(8*N*10^50:Nat)-(point N q D:ℝ)/D|≤_ at hr
  calc
    _ ≤ |Real.pi*(q:ℝ)/(8*N)-(numerator50*q:Nat)/(8*N*10^50:Nat)|+
      |(numerator50*q:Nat)/(8*N*10^50:Nat)-(point N q D:ℝ)/D| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
        (Real.pi*(q:ℝ)/(8*N)) ((numerator50*q:Nat)/(8*N*10^50:Nat):ℝ) ((point N q D:ℝ)/D)
    _ ≤ _ := (add_le_add hp hr).trans_eq (by ring)
end RHFastKernelChirpSeed

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelGaussianIntegerPower
noncomputable def square (z : Int×Int) : Int×Int := (z.1*z.1-z.2*z.2,2*z.1*z.2)
noncomputable def value (z : Int×Int) : ℂ := (z.1:ℂ)+(z.2:ℂ)*I
lemma square_value (z : Int×Int) : value (square z)=(value z)^2 := by
  simp only [value,square,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  ring_nf
  simp only [I_sq]
  ring
lemma pow8_value (c s : Nat) : value (square (square (square ((c:Int),(s:Int)))))=
    ((c:ℂ)+(s:ℂ)*I)^8 := by
  rw [square_value,square_value,square_value]
  simp only [value,Int.cast_natCast]
  ring
lemma rounded8_error (c s D S : Nat) (hD : 0 < D) (hS : 0 < S) :
    let w := square (square (square ((c:Int),(s:Int))))
    ‖(((c:ℂ)+(s:ℂ)*I)/(D:ℂ))^8-
      (((w.1*(S:Int)/(D:Int)^8:Int):ℂ)+
        ((w.2*(S:Int)/(D:Int)^8:Int):ℂ)*I)/(S:ℂ)‖≤2/(S:ℝ) := by
  intro w
  have h := RHFastKernelDyadicRounding.int_complex_rounding_error w.1 w.2 (D^8) S (by positivity) hS
  have hw : value w=((c:ℂ)+(s:ℂ)*I)^8 := pow8_value c s
  simp only [Nat.cast_pow] at h
  change ‖value w/(D:ℂ)^8-_‖≤_ at h
  rw [hw,←div_pow] at h
  exact h
end RHFastKernelGaussianIntegerPower

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHFastKernelChirpPairEnclosure
open RHFastKernelChirpSeed RHFastKernelExpEnclosure RHFastKernelGenericExpHorner RHFastKernelGaussianIntegerPower
lemma cos_guard (D d : Nat)
    (hc : 0 < (cosNumerator D d*D/denominator D)) :
    d^2*horner (cn D) (d^4)≤horner (cp D) (d^4) := by
  have hp : 0 < cosNumerator D d := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz] at hc
    simp at hc
  exact (Nat.sub_pos_iff_lt.mp hp).le
lemma sin_guard (D d : Nat)
    (hs : d=0 ∨ 0 < (sinNumerator D d*D/denominator D)) :
    d^2*horner (sn D) (d^4)≤horner (sp D) (d^4) := by
  rcases hs with rfl|hs
  · simp
  · have hp : 0 < horner (sp D) (d^4)-d^2*horner (sn D) (d^4) := by
      by_contra h
      have hz := Nat.eq_zero_of_not_pos h
      simp only [sinNumerator,hz,mul_zero,zero_mul,Nat.zero_div] at hs
      omega
    exact (Nat.sub_pos_iff_lt.mp hp).le
lemma small_phase_error (N q : Nat) (hN : 0 < N) (hq : q≤N)
    (hd : 2*point N q (2^112)≤2^112)
    (hc : 0 < (cosNumerator (2^112) (point N q (2^112))*(2^112)/denominator (2^112)))
    (hs : point N q (2^112)=0 ∨
      0 < (sinNumerator (2^112) (point N q (2^112))*(2^112)/denominator (2^112))) :
    ‖approximation (2^112) (point N q (2^112))-
      Complex.exp (I*((Real.pi*(q:ℝ)/(8*(N:ℝ)):ℝ):ℂ))‖≤1/10^32 := by
  let d := point N q (2^112)
  let θ := Real.pi*(q:ℝ)/(8*(N:ℝ))
  have h0 := enclosure (2^112) d (by norm_num) hd (cos_guard _ _ hc) (sin_guard _ _ hs)
  have h1 := quantization_error N q (2^112) hN (by norm_num) hq
  have h2 := phase_lipschitz ((d:ℝ)/(2:ℝ)^112) θ
  simp only [Nat.cast_pow,Nat.cast_ofNat] at h0 h1
  have he : Complex.exp (((d:ℂ)/(2:ℂ)^112)*I)=
      Complex.exp (I*(((d:ℝ)/(2:ℝ)^112:ℝ):ℂ)) := by congr 1;push_cast;ring
  rw [he] at h0
  rw [abs_sub_comm] at h2
  have h3 := h2.trans h1
  calc
    _ ≤ ‖approximation (2^112) d-Complex.exp (I*(((d:ℝ)/(2:ℝ)^112:ℝ):ℂ))‖+
      ‖Complex.exp (I*(((d:ℝ)/(2:ℝ)^112:ℝ):ℂ))-Complex.exp (I*(θ:ℂ))‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2/(2:ℝ)^112+1/10^40)+(1/(2:ℝ)^112+1/10^50) := add_le_add h0 h3
    _ ≤ _ := by norm_num
lemma phase_power_error (N q : Nat) (a : ℂ) (hN : 0 < N)
    (ha : ‖a-Complex.exp (I*((Real.pi*(q:ℝ)/(8*(N:ℝ)):ℝ):ℂ))‖≤1/10^32) :
    ‖a^8-Complex.exp (I*((Real.pi*(q:ℝ)/(N:ℝ):ℝ):ℂ))‖≤255/10^32 := by
  let w := Complex.exp (I*((Real.pi*(q:ℝ)/(8*(N:ℝ)):ℝ):ℂ))
  have hw : ‖w‖=1 := by
    dsimp [w]
    rw [Complex.norm_exp,mul_re,I_re,I_im,ofReal_re,ofReal_im]
    norm_num
  have hn : ‖a‖≤2 := by
    have he := norm_sub_le_norm_sub_add_norm_sub a w 0
    simp only [sub_zero,hw] at he
    linarith
  have hp := power_error a w (1/10^32) (by positivity) hn hw.le ha 8
  have he : w^8=Complex.exp (I*((Real.pi*(q:ℝ)/(N:ℝ):ℝ):ℂ)) := by
    dsimp [w]
    rw [←Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at hp
  norm_num at hp ⊢
  exact hp
end RHFastKernelChirpPairEnclosure

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
open scoped ComplexConjugate
namespace RHFastKernelSignedPhase
noncomputable def sign (neg : Bool) (z : ℂ) : ℂ := if neg then conj z else z
noncomputable def angle (neg : Bool) (x : ℝ) : ℝ := if neg then -x else x
lemma sign_exp (neg : Bool) (x : ℝ) :
    sign neg (Complex.exp (I*(x:ℂ)))=Complex.exp (I*(angle neg x:ℂ)) := by
  cases neg
  · rfl
  · simp only [sign,angle,Bool.false_eq_true,if_false,Bool.true_eq,if_true]
    rw [←Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,Complex.ofReal_neg]
    ring
lemma sign_error (neg : Bool) (a b : ℂ) : ‖sign neg a-sign neg b‖=‖a-b‖ := by
  cases neg
  · rfl
  · simp only [sign,Bool.true_eq,if_true,←map_sub,Complex.norm_conj]
lemma signed_power_error (neg : Bool) (a : ℂ) (x : ℝ)
    (ha : ‖a-Complex.exp (I*(x:ℂ))‖≤1/10^37) :
    ‖sign neg (a^8)-Complex.exp (I*(angle neg (8*x):ℂ))‖≤255/10^37 := by
  rw [←sign_exp,sign_error]
  exact RHFastKernelGammaPhase.power8_error a x ha
lemma small_phase_error (d : Nat) (hd : 2*d≤2^128)
 :
    ‖RHFastKernelExpEnclosure.approximation (2^128) d-
      Complex.exp (I*(((d:ℝ)/(2:ℝ)^128:ℝ):ℂ))‖≤1/10^37 := by
  have hg := TaoFivePrimes.rh_fast_kernel_gamma_trig_guards d hd
  have h := RHFastKernelExpEnclosure.enclosure (2^128) d (by norm_num) hd hg.1 hg.2.1
  have he : ((d:ℂ)/((2^128:Nat):ℂ))*I=I*(((d:ℝ)/(2:ℝ)^128:ℝ):ℂ) := by push_cast;ring
  rw [he] at h
  exact h.trans (by norm_num)
end RHFastKernelSignedPhase

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelPhaseQuantization
open RHFastKernelDyadicRounding
lemma floor_scaled_error (a b D : Nat) (hb : 0 < b) (hD : 0 < D) :
    |(a:ℝ)/(D:ℝ)-(b:ℝ)*(a/b:Nat)/(D:ℝ)|≤(b:ℝ)/(D:ℝ) := by
  have hb' : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have he : (a:ℝ)/(D:ℝ)-(b:ℝ)*(a/b:Nat)/(D:ℝ)=
      ((b:ℝ)/(D:ℝ))*((a:ℝ)/(b:ℝ)-(a/b:Nat)) := by field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(b:ℝ)/(D:ℝ))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (nat_division_error a b hb)
    (by positivity : (0:ℝ)≤(b:ℝ)/(D:ℝ))
lemma signed_error (a : Int) (Q D : Nat) (hQ : 0 < Q) (hD : 0 < D) :
    |(a:ℝ)/((D:ℝ)*(Q:ℝ))-
      (if a<0 then -(8:ℝ) else 8)*(a.natAbs/(8*Q):Nat)/(D:ℝ)|≤8/(D:ℝ) := by
  have hQ' : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have habs : (a.natAbs:ℝ)=|(a:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have h := floor_scaled_error a.natAbs (8*Q) (D*Q) (by positivity) (by positivity)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  have hright : (8*(Q:ℝ))/((D:ℝ)*(Q:ℝ))=8/(D:ℝ) := by field_simp
  rw [hright,habs] at h
  by_cases hn : a<0
  · have hn' : (a:ℝ)<0 := by exact_mod_cast hn
    rw [if_pos hn]
    rw [abs_of_neg hn'] at h
    have he : (a:ℝ)/((D:ℝ)*(Q:ℝ))-(-8)*(a.natAbs/(8*Q):Nat)/(D:ℝ)=
        -((-(a:ℝ))/((D:ℝ)*(Q:ℝ))-(8*(Q:ℝ))*(a.natAbs/(8*Q):Nat)/((D:ℝ)*(Q:ℝ))) := by field_simp;ring
    rw [he,abs_neg]
    exact h
  · have hn' : (0:ℝ)≤a := by exact_mod_cast (le_of_not_gt hn)
    rw [if_neg hn]
    rw [abs_of_nonneg hn'] at h
    have he : (8*(Q:ℝ))*(a.natAbs/(8*Q):Nat)/((D:ℝ)*(Q:ℝ))=
        8*(a.natAbs/(8*Q):Nat)/(D:ℝ) := by field_simp
    rw [he] at h
    exact h
end RHFastKernelPhaseQuantization

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaPhaseTarget
open RHFastKernelSignedPhase RHFastKernelGammaArithmetic RHFastKernelLogData
noncomputable def residual (ii k : Int) : Int := ii*10^50-2*(P:Int)*k*(D:Int)
noncomputable def input (ii k : Int) : Nat := (residual ii k).natAbs/(8*10^50)
noncomputable def negative (ii k : Int) : Bool := decide (residual ii k<0)
lemma quantization (ii k : Int) :
    |(ii:ℝ)/(D:ℝ)-2*((P:ℝ)/10^50)*(k:ℝ)-
      angle (negative ii k) (8*(input ii k:ℝ)/(D:ℝ))|≤8/(D:ℝ) := by
  have h := RHFastKernelPhaseQuantization.signed_error (residual ii k) (10^50) D (by norm_num) (by decide)
  have he : (residual ii k:ℝ)/((D:ℝ)*(10^50:Nat))=
      (ii:ℝ)/(D:ℝ)-2*((P:ℝ)/10^50)*(k:ℝ) := by
    unfold residual
    push_cast
    field_simp [show (D:ℝ)≠0 by norm_num [D]]
    ring
  have ha : (if residual ii k<0 then -(8:ℝ) else 8)*
      ((residual ii k).natAbs/(8*10^50):Nat)/(D:ℝ)=
      angle (negative ii k) (8*(input ii k:ℝ)/(D:ℝ)) := by
    unfold angle negative input
    by_cases hn : residual ii k<0 <;> simp only [hn,decide_true,decide_false,Bool.false_eq_true,Bool.true_eq,if_true,if_false] <;> ring
  rw [he,ha] at h
  exact h
lemma target_error (ii k : Int) (hk : |(k:ℝ)|≤10000000000)
    (hd : 2*input ii k≤2^128)
 :
    ‖sign (negative ii k) (RHFastKernelExpEnclosure.approximation (2^128) (input ii k))^8-
      Complex.exp (I*((ii:ℂ)/(D:ℂ)))‖≤3/10^35 := by
  let d := input ii k
  have h0 := small_phase_error d hd
  have h1 := signed_power_error (negative ii k) (RHFastKernelExpEnclosure.approximation (2^128) d)
    ((d:ℝ)/(2:ℝ)^128) h0
  have hsPow : sign (negative ii k) (RHFastKernelExpEnclosure.approximation (2^128) d)^8=
      sign (negative ii k) ((RHFastKernelExpEnclosure.approximation (2^128) d)^8) := by
    cases negative ii k <;> simp [sign,map_pow]
  rw [hsPow]
  have ha : 8*((d:ℝ)/(2:ℝ)^128)=8*(d:ℝ)/(D:ℝ) := by simp only [D,Nat.cast_pow,Nat.cast_ofNat];ring
  rw [ha] at h1
  have hp : |(P:ℝ)/10^50-Real.pi|≤1/10^50 := by
    rw [abs_sub_comm]
    exact piInput_error
  have h2 := RHFastKernelGammaPhase.reduction_error ((ii:ℝ)/(D:ℝ))
    (angle (negative ii k) (8*(d:ℝ)/(D:ℝ))) ((P:ℝ)/10^50) k D (by decide) hp hk (quantization ii k)
  simp only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast] at h2
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add h1 ((norm_sub_rev _ _).trans_le h2))).trans (by norm_num [D])
end RHFastKernelGammaPhaseTarget

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelFixedPoint
open Complex RHFastKernelDyadicRounding RHFastKernelExpPerturbation
noncomputable def step (D a : Nat) : Nat := a*a/D
noncomputable def iter (D : Nat) (a : Nat) : Nat→Nat
  | 0 => a
  | n+1 => step D (iter D a n)
lemma step_round (D a : Nat) (hD : 0 < D) :
    ‖((step D a:ℂ)/(D:ℂ))-((a:ℂ)/(D:ℂ))^2‖≤1/(D:ℝ) := by
  have h := scaled_rounding_error (a*a) (D*D) D (by positivity) hD
  have hi : a*a*D/(D*D)=a*a/D := by
    rw [show a*a*D=D*(a*a) by ring,show D*D=D*D by rfl,Nat.mul_div_mul_left _ _ hD]
  rw [hi] at h
  simpa only [step,div_pow,pow_two,←Complex.ofReal_natCast,←Complex.ofReal_mul,
    ←Complex.ofReal_div,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm,Nat.cast_mul,div_mul_div_comm] using h
lemma iteration_error (D a : Nat) (hD : 0 < D) (w : ℂ) (hw : ‖w‖≤1)
    (ε : ℝ) (hε : 1/(D:ℝ)≤ε) (he : ‖(a:ℂ)/(D:ℂ)-w‖≤ε)
    (n : Nat) (hn : (4:ℝ)^n*ε≤1) :
    ‖(iter D a n:ℂ)/(D:ℂ)-w^(2^n)‖≤(4:ℝ)^n*ε := by
  have hε0 : 0≤ε := le_trans (by positivity) hε
  induction n with
  | zero => simpa [iter] using he
  | succ n ih =>
    have hp : (4:ℝ)^n*ε≤1 := by
      have hm : (4:ℝ)^n≤4^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact (mul_le_mul_of_nonneg_right hm hε0).trans hn
    have hx := ih hp
    have hw' : ‖w^(2^n)‖≤1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hw
    have hs := square_error ((iter D a n:ℂ)/(D:ℂ)) (w^(2^n)) ((4:ℝ)^n*ε)
      ⟨by positivity,hp⟩ hw' hx
    have hr := step_round D (iter D a n) hD
    have hsmall : 1/(D:ℝ)≤(4:ℝ)^n*ε :=
      hε.trans (le_mul_of_one_le_left hε0 (one_le_pow₀ (by norm_num)))
    calc
      _ = ‖(step D (iter D a n):ℂ)/(D:ℂ)-(w^(2^n))^2‖ := by
        rw [iter,show (2:Nat)^(n+1)=2^n*2 by rw [pow_succ],pow_mul]
      _ ≤ ‖(step D (iter D a n):ℂ)/(D:ℂ)-((iter D a n:ℂ)/(D:ℂ))^2‖+
          ‖((iter D a n:ℂ)/(D:ℂ))^2-(w^(2^n))^2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1/(D:ℝ)+3*((4:ℝ)^n*ε) := add_le_add hr hs
      _ ≤ (4:ℝ)^n*ε+3*((4:ℝ)^n*ε) := add_le_add_left hsmall _
      _ = _ := by rw [pow_succ];ring
end RHFastKernelFixedPoint

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaAmplitude
open RHFastKernelGenericExpHorner RHFastKernelNegativeExp RHFastKernelFixedPoint
lemma amplitude_error (d : Nat) (hd : 2*d≤2^128)
    (hp : d*horner (en (2^128)) (d^2)≤horner (ep (2^128)) (d^2)) :
    ‖(iter (2^128) (seed (2^128) d) 8:ℂ)/(2:ℂ)^128-
      Complex.exp ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)‖≤1/10^32 := by
  let D : Nat := 2^128
  let w : ℂ := Complex.exp (-(d:ℂ)/(D:ℂ))
  have hw : ‖w‖≤1 := by
    dsimp only [w]
    have hex : -(d:ℂ)/(D:ℂ)=((-(d:ℝ)/(D:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [hex,Complex.norm_exp,Complex.ofReal_re]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by positivity)
  have he := enclosure D d (by norm_num [D]) hd hp
  have h := iteration_error D (seed D d) (by norm_num [D]) w hw
    (1/(D:ℝ)+1/10^40) (by norm_num [D]) he 8 (by norm_num [D])
  have hh : w^((2:Nat)^8)=Complex.exp ((-256*(d:ℝ)/(D:ℝ):ℝ):ℂ) := by
    dsimp only [w]
    rw [←Complex.exp_nat_mul]
    congr 1
    push_cast
    norm_num
    ring
  rw [hh] at h
  have h' := h.trans (by norm_num [D] : (4:ℝ)^8*(1/(D:ℝ)+1/10^40)≤1/10^32)
  simpa only [D,Nat.cast_pow,Nat.cast_ofNat] using h'
end RHFastKernelGammaAmplitude

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaAmplitude
open RHFastKernelGenericExpHorner RHFastKernelNegativeExp RHFastKernelFixedPoint RHFastKernelExpPerturbation
lemma target_error (rr : Int) (hr : rr≤0) (d : Nat)
    (heq : d=(-rr).toNat/256) (hd : 2*d≤2^128)
    (hp : d*horner (en (2^128)) (d^2)≤horner (ep (2^128)) (d^2)) :
    ‖(iter (2^128) (seed (2^128) d) 8:ℂ)/(2:ℂ)^128-
      Complex.exp ((rr:ℂ)/(2:ℂ)^128)‖≤2/10^32 := by
  have hnat : ((-rr).toNat:ℝ)=-(rr:ℝ) := by
    have he := Int.toNat_of_nonneg (show (0:Int)≤-rr by omega)
    exact_mod_cast he
  have h := RHFastKernelPhaseQuantization.floor_scaled_error (-rr).toNat 256 (2^128) (by norm_num) (by norm_num)
  rw [←heq,hnat] at h
  simp only [Nat.cast_pow,Nat.cast_ofNat] at h
  have hdif : |(rr:ℝ)/(2:ℝ)^128-(-256*(d:ℝ)/(2:ℝ)^128)|≤256/(2:ℝ)^128 := by
    convert h using 1
    rw [←abs_neg]
    congr 1
    ring
  have hex : ‖Complex.exp ((rr:ℂ)/(2:ℂ)^128)‖≤1 := by
    have he : (rr:ℂ)/(2:ℂ)^128=(((rr:ℝ)/(2:ℝ)^128:ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_exp,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hr) (by positivity))
  have hc : ‖((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)-(rr:ℂ)/(2:ℂ)^128‖≤256/(2:ℝ)^128 := by
    have he : ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)-(rr:ℂ)/(2:ℂ)^128=
        ((-256*(d:ℝ)/(2:ℝ)^128-(rr:ℝ)/(2:ℝ)^128:ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact hdif
  have hh := exp_error ((rr:ℂ)/(2:ℂ)^128) (((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)) (hc.trans (by norm_num))
  have hb : ‖Complex.exp ((rr:ℂ)/(2:ℂ)^128)-
      Complex.exp ((-256*(d:ℝ)/(2:ℝ)^128:ℝ):ℂ)‖≤512/(2:ℝ)^128 := by
    apply hh.trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hex (by norm_num)) hc (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (amplitude_error d hd hp) ((norm_sub_rev _ _).trans_le hb))).trans (by norm_num)
end RHFastKernelGammaAmplitude

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelGammaArithmetic
open RHFastKernelLogData RHFastKernelExpEnclosure RHFastKernelFixedPoint
noncomputable def sampleIndex (i : Nat) : Int := (i:Int)-8192
noncomputable def sampleNumerator (T i : Nat) : Nat := ((T:Int)*32+sampleIndex i).toNat
lemma realPart_eq (T i : Nat) : (compute T i).realPart=
    round (realInput (sampleNumerator T i) (sampleIndex i) (logInput (sampleNumerator T i))) := rfl
lemma phase_eq (T i : Nat) : (compute T i).phase=
    round (phaseInput (sampleNumerator T i) (logInput (sampleNumerator T i))) := rfl
lemma phaseInput_eq (T i : Nat) : (compute T i).phaseInput=
    RHFastKernelGammaPhaseTarget.input (compute T i).phase (compute T i).period := rfl
lemma negative_eq (T i : Nat) : (compute T i).negative=
    RHFastKernelGammaPhaseTarget.negative (compute T i).phase (compute T i).period := rfl
lemma expInput_eq (T i : Nat) : (compute T i).expInput=(-(compute T i).realPart).toNat/256 := rfl
lemma expSeed_eq (T i : Nat) : (compute T i).expSeed=RHFastKernelNegativeExp.seed D (compute T i).expInput := rfl
lemma phaseCS_eq (d : Nat) : phaseCS d=
    (cosNumerator D d*D/RHFastKernelExpEnclosure.denominator D,sinNumerator D d*D/RHFastKernelExpEnclosure.denominator D) := by
  unfold phaseCS cosNumerator sinNumerator RHFastKernelExpEnclosure.denominator
  rw [show Nat.factorial 31=8222838654177922817725562880000000 by norm_num]
lemma cos_eq (T i : Nat) : (compute T i).cos=cosNumerator D (compute T i).phaseInput*D/RHFastKernelExpEnclosure.denominator D := by
  change (phaseCS (compute T i).phaseInput).1=_
  rw [phaseCS_eq]
lemma sin_eq (T i : Nat) : (compute T i).sin=sinNumerator D (compute T i).phaseInput*D/RHFastKernelExpEnclosure.denominator D := by
  change (phaseCS (compute T i).phaseInput).2=_
  rw [phaseCS_eq]
lemma range_iteration (D a n : Nat) :
    (List.range n).foldl (fun z _ => z*z/D) a=iter D a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,ih]
    rfl
lemma amplitude_eq (T i : Nat) : (compute T i).amplitude=
    iter D (RHFastKernelNegativeExp.seed D (compute T i).expInput) 8 := by
  change (List.range 8).foldl (fun z _ => z*z/D) (compute T i).expSeed=_
  rw [range_iteration,expSeed_eq]
lemma exp_guard (D d : Nat) (h : 0 < RHFastKernelNegativeExp.seed D d) :
    d*RHFastKernelGenericExpHorner.horner (RHFastKernelNegativeExp.en D) (d^2)≤
      RHFastKernelGenericExpHorner.horner (RHFastKernelNegativeExp.ep D) (d^2) := by
  have hpos : 0 < RHFastKernelNegativeExp.numerator D d := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    simp only [RHFastKernelNegativeExp.seed,hz,zero_mul,Nat.zero_div] at h
    omega
  exact (Nat.sub_pos_iff_lt.mp hpos).le
lemma numerator_bounds (T i : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (hi : i<16384) :
    96000000000≤ sampleNumerator T i ∧ sampleNumerator T i≤128000000000 := by
  unfold sampleNumerator sampleIndex
  omega
end RHFastKernelGammaArithmetic

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000

set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHFastKernelGammaPolynomial
open RHFastKernelExpPerturbation RHFastKernelGammaArithmetic RHFastKernelLogData
lemma product_exp_error (amp ph : ℂ) (rr ii : ℝ) (hr : rr≤0)
    (ha : ‖amp-Complex.exp (rr:ℂ)‖≤2/10^32)
    (hp : ‖ph-Complex.exp (I*(ii:ℂ))‖≤3/10^35) :
    ‖amp*ph-Complex.exp ((rr:ℂ)+(ii:ℂ)*I)‖≤5/10^32 := by
  have hn : ‖Complex.exp (rr:ℂ)‖≤1 := by
    rw [Complex.norm_exp,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr hr
  have hph : ‖ph‖≤2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub ph (Complex.exp (I*(ii:ℂ))) 0
    have he : ‖Complex.exp (I*(ii:ℂ))‖=1 := by
      simpa only [mul_comm] using Complex.norm_exp_I_mul_ofReal ii
    simp only [sub_zero,he] at h
    linarith
  rw [show (rr:ℂ)+(ii:ℂ)*I=(rr:ℂ)+I*(ii:ℂ) by ring,Complex.exp_add]
  have he : amp*ph-Complex.exp (rr:ℂ)*Complex.exp (I*(ii:ℂ))=
      (amp-Complex.exp (rr:ℂ))*ph+Complex.exp (rr:ℂ)*(ph-Complex.exp (I*(ii:ℂ))) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  exact (add_le_add (mul_le_mul ha hph (norm_nonneg _) (by positivity))
    (mul_le_mul hn hp (norm_nonneg _) (by norm_num))).trans (by norm_num)
lemma full_gamma_error (bn : Nat) (n : Int) (amp ph : ℂ)
    (hbn : 96000000000≤bn ∧ bn≤128000000000)
    (hr : (round (realInput bn n (logInput bn)):ℝ)/D≤0)
    (ha : ‖amp-Complex.exp ((round (realInput bn n (logInput bn)):ℂ)/(D:ℂ))‖≤2/10^32)
    (hp : ‖ph-Complex.exp (I*((round (phaseInput bn (logInput bn)):ℂ)/(D:ℂ)))‖≤3/10^35) :
    ‖Complex.Gamma (1/4+((bn:ℂ)/64)*I)*
      Complex.exp (((Real.pi*((bn:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ))-amp*ph‖≤1/10^25 := by
  have h1 := gamma_input_error bn n hbn
  have h2 := product_exp_error amp ph
    ((round (realInput bn n (logInput bn)):ℝ)/D)
    ((round (phaseInput bn (logInput bn)):ℝ)/D) hr
    (by simpa only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast] using ha)
    (by simpa only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast] using hp)
  simp only [Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast] at h2
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add h1 ((norm_sub_rev _ _).trans_le h2))).trans (by norm_num)
end RHFastKernelGammaPolynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
namespace RHFastKernelGammaAllSamples
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelSignedPhase
noncomputable def raw (T i : Nat) : ℂ :=
  ((compute T i).amplitude:ℂ)/(D:ℂ)*
    sign (compute T i).negative (RHFastKernelExpEnclosure.approximation D (compute T i).phaseInput)^8
lemma enclosure (T i : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (hi : i<16384) :
    ‖Complex.Gamma (1/4+((sampleNumerator T i:ℂ)/64)*I)*
      Complex.exp (((Real.pi*((sampleNumerator T i:ℝ)/64)/2-((sampleIndex i:ℝ)/32)^2/800:ℝ):ℂ))-
      raw T i‖≤1/10^25 := by
  have hb := TaoFivePrimes.rh_fast_kernel_gamma_base_guards T i (by omega) (by omega) hi
  rcases hb with ⟨hr,_,hk,hPhase,hExp⟩
  have he := TaoFivePrimes.rh_fast_kernel_gamma_exp_guards (compute T i).expInput hExp
  have hSeed : 0<(compute T i).expSeed := he.1
  have hki : |((compute T i).period:ℝ)|≤10000000000 := by
    have h : ((compute T i).period.natAbs:ℝ)≤10000000000 := by exact_mod_cast hk
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have hneg := exp_guard D (compute T i).expInput (by rw [←expSeed_eq];exact hSeed)
  have ha := RHFastKernelGammaAmplitude.target_error (compute T i).realPart hr (compute T i).expInput
    (expInput_eq T i) hExp hneg
  have hp := RHFastKernelGammaPhaseTarget.target_error (compute T i).phase (compute T i).period hki
    (by simpa only [←phaseInput_eq T i,D] using hPhase)
  simp only [←phaseInput_eq T i,←negative_eq T i] at hp
  have hrr : (round (realInput (sampleNumerator T i) (sampleIndex i) (logInput (sampleNumerator T i))):ℝ)/D≤0 := by
    rw [←realPart_eq]
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hr) (by norm_num [D])
  have ha' : ‖((compute T i).amplitude:ℂ)/(D:ℂ)-
      Complex.exp ((round (realInput (sampleNumerator T i) (sampleIndex i) (logInput (sampleNumerator T i))):ℂ)/(D:ℂ))‖≤2/10^32 := by
    rw [←realPart_eq]
    rw [amplitude_eq T i]
    simpa only [D,Nat.cast_pow,Nat.cast_ofNat] using ha
  have hp' : ‖sign (compute T i).negative (RHFastKernelExpEnclosure.approximation D (compute T i).phaseInput)^8-
      Complex.exp (I*((round (phaseInput (sampleNumerator T i) (logInput (sampleNumerator T i))):ℂ)/(D:ℂ)))‖≤3/10^35 := by
    rw [←phase_eq]
    exact hp
  exact RHFastKernelGammaPolynomial.full_gamma_error (sampleNumerator T i) (sampleIndex i)
    (((compute T i).amplitude:ℂ)/(D:ℂ))
    (sign (compute T i).negative (RHFastKernelExpEnclosure.approximation D (compute T i).phaseInput)^8)
    (numerator_bounds T i hT hU hi) hrr ha' hp'
end RHFastKernelGammaAllSamples
end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex

theorem solution (T i : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (hi : i<16384) :
  let n : Int := (i:Int)-8192
  let b : Nat := ((T:Int)*32+n).toNat
  let v := RHFastKernelGammaArithmetic.compute T i
  let D : Nat := RHFastKernelLogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))-
    ((v.amplitude:ℂ)/(D:ℂ))*phase^8‖≤1/10^25 := by
  dsimp only
  have h := RHFastKernelGammaAllSamples.enclosure T i hT hU hi
  simpa only [RHFastKernelGammaAllSamples.raw,RHFastKernelSignedPhase.sign,
    RHFastKernelExpEnclosure.approximation,←RHFastKernelGammaArithmetic.cos_eq T i,
    ←RHFastKernelGammaArithmetic.sin_eq T i,RHFastKernelGammaArithmetic.sampleIndex,
    RHFastKernelGammaArithmetic.sampleNumerator] using h
#print axioms solution
