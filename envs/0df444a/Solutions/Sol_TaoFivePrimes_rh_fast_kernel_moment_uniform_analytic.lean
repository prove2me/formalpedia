-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_moment_uniform_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:18:46.473124+00:00
-- url     : https://prove2.me/submissions/3f6c2cfe-8b5b-4496-b519-86237d5fcbc5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 20000
open Complex
namespace RHFastMomentDyadicRounding
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
end RHFastMomentDyadicRounding

namespace RHFastMomentDyadicRounding
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
end RHFastMomentDyadicRounding

namespace RHFastMomentDyadicRounding
end RHFastMomentDyadicRounding

namespace RHFastMomentDyadicRounding
end RHFastMomentDyadicRounding

namespace RHFastMomentPiSeed
noncomputable def numerator50 : Nat := 314159265358979323846264338327950288419716939937510
lemma seed50 : (numerator50:ℝ)/10^50≤Real.pi ∧
    Real.pi≤(numerator50+1:ℝ)/10^50 := by
  have hp := TaoFivePrimes.rh_pi_enclosure_700
  have hl : (numerator50:ℝ)/10^50≤(TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  have hu : (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700≤(numerator50+1:ℝ)/10^50 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  exact ⟨hl.trans hp.1,hp.2.trans hu⟩
end RHFastMomentPiSeed

namespace RHFastMomentGaussianIntegerPower
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
  have h := RHFastMomentDyadicRounding.int_complex_rounding_error w.1 w.2 (D^8) S (by positivity) hS
  have hw : value w=((c:ℂ)+(s:ℂ)*I)^8 := pow8_value c s
  simp only [Nat.cast_pow] at h
  change ‖value w/(D:ℂ)^8-_‖≤_ at h
  rw [hw,←div_pow] at h
  exact h
end RHFastMomentGaussianIntegerPower

namespace RHFastMomentGaussianIntegerPower
end RHFastMomentGaussianIntegerPower

namespace RHFastMomentMomentFactor
noncomputable def factor (t : ℝ) (k : Nat) : ℂ :=
  (-2*(Real.pi:ℂ)*I*(t:ℂ))^k/((k.factorial:ℂ)*(512:ℂ)^k)
lemma factor_bound (t : ℝ) (k : Nat) (ht : |t|≤256) : ‖factor t k‖≤81 := by
  have hp : 0≤Real.pi*|t|/256 := by positivity
  have hu : Real.pi*|t|/256≤4 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  have hh : ‖factor t k‖=(Real.pi*|t|/256)^k/(k.factorial:ℝ) := by
    unfold factor
    simp only [norm_div,norm_pow,norm_mul,norm_natCast,norm_ofNat]
    simp only [norm_mul,norm_neg,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    rw [div_pow]
    field_simp
    rw [show (512:ℝ)^k=(2:ℝ)^k*256^k by rw [←mul_pow];norm_num]
    ring
  rw [hh]
  calc
    _ ≤ Real.exp (Real.pi*|t|/256) := Real.pow_div_factorial_le_exp _ hp k
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hu
    _ = (Real.exp 1)^4 := by simpa using (Real.exp_nat_mul (1:ℝ) (4:Nat)).symm
    _ ≤ (3:ℝ)^4 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
    _ = 81 := by norm_num
end RHFastMomentMomentFactor

namespace RHFastMomentPowerPerturbation
lemma power_error (a b : ℂ) (M ε : ℝ) (hM : 1≤M) (hε : 0≤ε)
    (ha : ‖a‖≤M) (hb : ‖b‖≤M) (he : ‖a-b‖≤ε) (n : Nat) :
    ‖a^n-b^n‖≤(2*M)^n*ε := by
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have hmn : M^n≤(2*M)^n := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hs : M^n≤M*(2*M)^n :=
      hmn.trans (le_mul_of_one_le_left (by positivity) hM)
    calc
      _ = ‖(a-b)*a^n+b*(a^n-b^n)‖ := by congr 1;ring
      _ ≤ ‖(a-b)*a^n‖+‖b*(a^n-b^n)‖ := norm_add_le _ _
      _ ≤ ε*M^n+M*((2*M)^n*ε) := by
        rw [norm_mul,norm_mul,norm_pow]
        exact add_le_add (mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) ha _)
          (by positivity) hε) (mul_le_mul hb ih (norm_nonneg _) (by linarith))
      _ ≤ ε*(M*(2*M)^n)+M*((2*M)^n*ε) := by gcongr
      _ = _ := by rw [pow_succ];ring
end RHFastMomentPowerPerturbation

namespace RHFastMomentMomentPi
open RHFastMomentMomentFactor
noncomputable def base (t p : ℝ) : ℂ := I*((-p*t/256:ℝ):ℂ)
noncomputable def seedFactor (t p : ℝ) (k : Nat) : ℂ := (base t p)^k/(k.factorial:ℂ)
lemma base_norm (t p : ℝ) (ht : |t|≤256) (hp : 0≤p ∧ p≤4) : ‖base t p‖≤4 := by
  rw [base,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_mul,abs_neg,abs_of_nonneg hp.1]
  norm_num
  nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr ht)]
lemma base_error (t p : ℝ) (ht : |t|≤256) (hp : |Real.pi-p|≤1/10^50) :
    ‖base t Real.pi-base t p‖≤1/10^50 := by
  have he : base t Real.pi-base t p=I*((-(Real.pi-p)*t/256:ℝ):ℂ) := by
    unfold base;push_cast;ring
  rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_div,abs_mul,abs_neg]
  norm_num
  nlinarith [mul_nonneg (abs_nonneg (Real.pi-p)) (sub_nonneg.mpr ht)]
lemma factor_eq (t : ℝ) (k : Nat) : factor t k=seedFactor t Real.pi k := by
  unfold factor seedFactor
  have he : -2*(Real.pi:ℂ)*I*(t:ℂ)=512*base t Real.pi := by
    unfold base
    push_cast
    ring
  rw [he,mul_pow]
  have hf : (k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hf]
lemma factor_error (t p : ℝ) (k : Nat) (ht : |t|≤256) (hk : k≤25)
    (hp : 0≤p ∧ p≤4) (he : |Real.pi-p|≤1/10^50) :
    ‖factor t k-seedFactor t p k‖≤1/10^27 := by
  have h := RHFastMomentPowerPerturbation.power_error (base t Real.pi) (base t p) 4 (1/10^50)
    (by norm_num) (by positivity)
    (base_norm t Real.pi ht ⟨Real.pi_pos.le,Real.pi_lt_four.le⟩)
    (base_norm t p ht hp) (base_error t p ht he) k
  rw [factor_eq,seedFactor,seedFactor,←sub_div,norm_div,Complex.norm_natCast]
  calc
    _ ≤ ‖(base t Real.pi)^k-(base t p)^k‖ :=
      div_le_self (norm_nonneg _) (by exact_mod_cast (show 1≤k.factorial from Nat.factorial_pos k))
    _ ≤ (2*4:ℝ)^k*(1/10^50) := h
    _ ≤ (8:ℝ)^25*(1/10^50) := by
      have hm := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤8) hk) (by positivity : (0:ℝ)≤1/10^50)
      norm_num at hm ⊢
      exact hm
    _ ≤ _ := by norm_num
end RHFastMomentMomentPi

namespace RHFastMomentMomentPi
lemma seeded_moment_error (gamma proposal rounded : ℂ) (t p : ℝ) (k : Nat)
    (ht : |t|≤256) (hk : k≤25) (hp : 0≤p ∧ p≤4)
    (hpi : |Real.pi-p|≤1/10^50) (hn : ‖gamma‖≤6)
    (he : ‖gamma-proposal‖≤1/10^25)
    (hr : ‖proposal*seedFactor t p k-rounded‖≤2/(2:ℝ)^80) :
    ‖gamma*RHFastMomentMomentFactor.factor t k-rounded‖≤1/10^23 := by
  have hpN : ‖proposal‖≤7 := by
    have h := norm_sub_le_norm_sub_add_norm_sub proposal gamma 0
    simp only [sub_zero,norm_sub_rev proposal gamma] at h
    linarith
  have h1 : ‖gamma*RHFastMomentMomentFactor.factor t k-proposal*RHFastMomentMomentFactor.factor t k‖≤81/10^25 := by
    rw [←sub_mul,norm_mul]
    exact (mul_le_mul he (RHFastMomentMomentFactor.factor_bound t k ht) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2 : ‖proposal*RHFastMomentMomentFactor.factor t k-proposal*seedFactor t p k‖≤7/10^27 := by
    rw [←mul_sub,norm_mul]
    exact (mul_le_mul hpN (factor_error t p k ht hk hp hpi) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add h1 ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h2 hr)))).trans (by norm_num)
end RHFastMomentMomentPi

namespace RHFastKernelMomentArithmetic
open RHFastKernelGammaArithmetic RHFastKernelLogData
noncomputable def value (z : Int×Int) : ℂ := (z.1:ℂ)+(z.2:ℂ)*I
noncomputable def raw (v : Record) : ℂ := value (rawPair v)/(D:ℂ)^9
noncomputable def rounded (i : Nat) (v : Record) (k : Nat) : ℂ := value (moment i v k)/(2:ℂ)^80
lemma rotate_value (z : Int×Int) (k : Nat) : value (rotate z k)=I^k*value z := by
  rw [Complex.I_pow_eq_pow_mod]
  have hk : k%4<4 := Nat.mod_lt _ (by decide)
  generalize h : k%4=j at hk ⊢
  interval_cases j <;> simp [rotate,h,value,Complex.I_sq,Complex.I_pow_three] <;> ring_nf <;> simp [Complex.I_sq]
lemma denominator_pos (k : Nat) : 0 < denominator k := by
  unfold denominator D
  positivity
lemma unrounded_moment (i : Nat) (v : Record) (k : Nat) :
    raw v*RHFastMomentMomentPi.seedFactor (((((i:Int)-8192: Int):ℝ)/32)) ((P:ℝ)/10^50) k =
      value (rotate (rawPair v) k)*((-(P:Int)*((i:Int)-8192):Int):ℂ)^k/(denominator k:ℂ) := by
  have he : RHFastMomentMomentPi.base (((((i:Int)-8192: Int):ℝ)/32)) ((P:ℝ)/10^50) =
      I*((-(P:Int)*((i:Int)-8192):Int):ℂ)/(8192*10^50:ℂ) := by
    unfold RHFastMomentMomentPi.base
    push_cast
    ring
  rw [rotate_value]
  unfold raw RHFastMomentMomentPi.seedFactor
  rw [he,div_pow,mul_pow]
  simp only [denominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

lemma rounding (i : Nat) (v : Record) (k : Nat) :
    ‖raw v*RHFastMomentMomentPi.seedFactor (((((i:Int)-8192: Int):ℝ)/32)) ((P:ℝ)/10^50) k-
      rounded i v k‖≤2/(2:ℝ)^80 := by
  have h := RHFastMomentDyadicRounding.int_complex_rounding_error
    ((rotate (rawPair v) k).1*(-(P:Int)*((i:Int)-8192))^k)
    ((rotate (rawPair v) k).2*(-(P:Int)*((i:Int)-8192))^k)
    (denominator k) (2^80) (denominator_pos k) (by positivity)
  rw [unrounded_moment]
  convert h using 1 <;> simp only [rounded,moment,value,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  ring
end RHFastKernelMomentArithmetic

namespace RHFastKernelMomentArithmetic
open RHFastKernelGammaArithmetic RHFastKernelLogData
lemma raw_gamma (v : Record) :
    raw v = ((v.amplitude:ℂ)/(D:ℂ))*
      (if v.negative then starRingEnd ℂ (((v.cos:ℂ)+(v.sin:ℂ)*I)/(D:ℂ))
       else (((v.cos:ℂ)+(v.sin:ℂ)*I)/(D:ℂ)))^8 := by
  let w := RHFastKernelGammaArithmetic.square (RHFastKernelGammaArithmetic.square
    (RHFastKernelGammaArithmetic.square ((v.cos:Int),(v.sin:Int))))
  have hw : value w=((v.cos:ℂ)+(v.sin:ℂ)*I)^8 :=
    RHFastMomentGaussianIntegerPower.pow8_value v.cos v.sin
  have hd : (D:ℂ)≠0 := by norm_num [D]
  have hc := congrArg (starRingEnd ℂ) hw
  simp only [map_pow,map_add,map_mul,Complex.conj_natCast,Complex.conj_I] at hc
  cases hb : v.negative
  · simp only [hb,Bool.false_eq_true,↓reduceIte,raw,rawPair]
    calc
      _ = (v.amplitude:ℂ)*value w/(D:ℂ)^9 := by
        simp only [value,Int.cast_mul,Int.cast_natCast]
        ring
      _ = _ := by
        rw [hw,div_pow]
        field_simp [hd]
  · simp only [hb,↓reduceIte,raw,rawPair]
    have hn : value ((v.amplitude:Int)*w.1,(v.amplitude:Int)*(-w.2)) =
        (v.amplitude:ℂ)*((w.1:ℂ)-(w.2:ℂ)*I) := by
      simp only [value,Int.cast_mul,Int.cast_natCast,Int.cast_neg]
      ring
    change value ((v.amplitude:Int)*w.1,(v.amplitude:Int)*(-w.2))/(D:ℂ)^9=_
    rw [hn]
    have hc' : (w.1:ℂ)-(w.2:ℂ)*I=((v.cos:ℂ)-(v.sin:ℂ)*I)^8 := by
      simpa only [value,map_add,map_mul,map_intCast,Complex.conj_I,mul_neg,sub_eq_add_neg] using hc
    rw [hc']
    simp only [map_div₀,map_add,map_mul,Complex.conj_natCast,Complex.conj_I,mul_neg,sub_eq_add_neg,div_pow]
    field_simp [hd]
end RHFastKernelMomentArithmetic


open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelMomentArithmetic

theorem solution (T i k : Nat) (hT : 3000000256≤T) (hU : T≤3999999744)
    (hi : i<16384) (hk : k<26) :
  let n : Int := (i:Int)-8192
  let b : Nat := ((T:Int)*32+n).toNat
  let v := RHFastKernelGammaArithmetic.compute T i
  let m := RHFastKernelMomentArithmetic.moment i v k
  ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))*
    ((-2*(Real.pi:ℂ)*Complex.I*((n:ℂ)/32))^k/
      ((k.factorial:ℂ)*(512:ℂ)^k))-
    ((m.1:ℂ)+(m.2:ℂ)*Complex.I)/(2:ℂ)^80‖≤1/10^23 := by
  let n : Int := (i:Int)-8192
  let b : Nat := ((T:Int)*32+n).toNat
  let v := RHFastKernelGammaArithmetic.compute T i
  let gamma : ℂ := Complex.Gamma (1/4+((b:ℂ)/64)*I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ))
  have ht : |(n:ℝ)/32|≤256 := by
    dsimp [n]
    rw [abs_le]
    push_cast
    constructor <;> linarith [show (i:ℝ)<16384 by exact_mod_cast hi,Nat.cast_nonneg (α:=ℝ) i]
  have hp : 0≤(P:ℝ)/10^50 ∧ (P:ℝ)/10^50≤4 := by norm_num [P]
  have hpi : |Real.pi-(P:ℝ)/10^50|≤1/10^50 := by
    have h := RHFastMomentPiSeed.seed50
    change |Real.pi-(RHFastMomentPiSeed.numerator50:ℝ)/10^50|≤1/10^50
    rw [abs_of_nonneg (by linarith [h.1])]
    linarith [h.2]
  have hnorm : ‖gamma‖≤6 := by
    have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 ((b:ℝ)/64)
    have hg' : ‖Complex.Gamma (1/4+((b:ℂ)/64)*I)‖*Real.exp (Real.pi*((b:ℝ)/64)/2)≤6 := by
      simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using hg
    have he : Real.exp (-(((n:ℝ)/32)^2/800))≤1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ((n:ℝ)/32)])
    dsimp [gamma]
    rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,sub_eq_add_neg,Real.exp_add,←mul_assoc]
    calc
      _ ≤ (6:ℝ)*1 := mul_le_mul hg' he (Real.exp_pos _).le (by norm_num)
      _ = 6 := by ring
  have hg := TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic T i hT hU hi
  have hraw : ‖gamma-raw v‖≤1/10^25 := by
    rw [raw_gamma]
    exact hg
  have h := RHFastMomentMomentPi.seeded_moment_error gamma (raw v) (rounded i v k)
    ((n:ℝ)/32) ((P:ℝ)/10^50) k ht (by omega) hp hpi hnorm hraw (rounding i v k)
  simpa only [RHFastMomentMomentFactor.factor,
    RHFastKernelMomentArithmetic.rounded,RHFastKernelMomentArithmetic.value,
    gamma,n,b,v,
    Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ofNat] using h
#print axioms solution
