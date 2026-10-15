-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_chirp_enclosures_16384
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T22:28:14.692583+00:00
-- url     : https://prove2.me/submissions/8475d1ba-c23b-4bd2-b465-6eed0395f83d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighChirpData16384
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex CauSeq Finset
namespace RHHighTaylor
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
end RHHighTaylor

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHHighGenericExpHorner
open Complex
lemma exp32_error (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖Complex.exp z-∑ k ∈ Finset.range 32, z^k/(k.factorial:ℂ)‖≤1/10^40 := by
  have hp : ‖z‖^32≤(1/2:ℝ)^32 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have he : Real.exp ‖z‖≤3 := le_trans (Real.exp_le_exp.mpr (by linarith)) Real.exp_one_lt_three.le
  calc
    _ ≤ (‖z‖^32/((32).factorial:ℝ))*Real.exp ‖z‖ := RHHighTaylor.exp_factorial_remainder z 32
    _ ≤ ((1/2:ℝ)^32/((32).factorial:ℝ))*3 := mul_le_mul
      (div_le_div_of_nonneg_right hp (by positivity)) he (by positivity) (by positivity)
    _ ≤ _ := by norm_num

def horner (cs : List Nat) (x : Nat) : Nat := cs.foldr (fun c p => c+x*p) 0
lemma cast_horner (cs : List Nat) (x : Nat) :
    ((horner cs x:Nat):ℝ)=(cs.map (fun c : Nat => (c:ℝ))).foldr (fun c p => c+(x:ℝ)*p) 0 := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    change ((c+x*horner cs x:Nat):ℝ)=_
    simp only [Nat.cast_add,Nat.cast_mul,List.map_cons,List.foldr_cons,ih]
def cp (D : Nat) : List Nat := [8222838654177922817725562880000000*D^31,342618277257413450738565120000000*D^27,203939450748460387344384000000*D^23,17166620433372086476800000*D^19,393008709555221760000*D^15,3379847863392000*D^11,13253058000*D^7,26970*D^3]
def cn (D : Nat) : List Nat := [4111419327088961408862781440000000*D^29,11420609241913781691285504000000*D^25,2265993897205115414937600000*D^21,94322090293253222400000*D^17,1284342188088960000*D^13,7315688016000*D^9,20389320*D^5,31*D^1]
def sp (D : Nat) : List Nat := [8222838654177922817725562880000000*D^30,68523655451482690147713024000000*D^26,22659938972051154149376000000*D^22,1320509264105545113600000*D^18,23118159385601280000*D^14,160945136352000*D^10,530122320*D^6,930*D^2]
def sn (D : Nat) : List Nat := [1370473109029653802954260480000000*D^28,1631515605987683098755072000000*D^24,205999445200465037721600000*D^20,6288139352883548160000*D^16,67596957267840000*D^12,318073392000*D^8,755160*D^4,1*D^0]
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
end RHHighGenericExpHorner

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighDyadicRounding
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
end RHHighDyadicRounding

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighExpEnclosure
open RHHighGenericExpHorner RHHighDyadicRounding
def cosNumerator (D d : Nat) : Nat := horner (cp D) (d^4)-d^2*horner (cn D) (d^4)
def sinNumerator (D d : Nat) : Nat := d*(horner (sp D) (d^4)-d^2*horner (sn D) (d^4))
def denominator (D : Nat) : Nat := D^31*(31).factorial
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
end RHHighExpEnclosure

set_option autoImplicit false
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
namespace RHHighPiSeed
def numerator50 : Nat := 314159265358979323846264338327950288419716939937510
lemma seed50 : (numerator50:ℝ)/10^50≤Real.pi ∧
    Real.pi≤(numerator50+1:ℝ)/10^50 := by
  have hp := TaoFivePrimes.rh_pi_enclosure_700
  have hl : (numerator50:ℝ)/10^50≤(TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  have hu : (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700≤(numerator50+1:ℝ)/10^50 := by
    norm_num [numerator50,TaoFivePrimes_RHPi700Numerator]
  exact ⟨hl.trans hp.1,hp.2.trans hu⟩
end RHHighPiSeed

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighChirpSeed
open RHHighPiSeed RHHighDyadicRounding RHHighExpEnclosure RHHighGenericExpHorner
def point (N q D : Nat) : Nat := numerator50*q*D/(8*N*10^50)
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
end RHHighChirpSeed

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighDyadicRounding
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
end RHHighDyadicRounding

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighGaussianIntegerPower
def square (z : Int×Int) : Int×Int := (z.1*z.1-z.2*z.2,2*z.1*z.2)
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
  have h := RHHighDyadicRounding.int_complex_rounding_error w.1 w.2 (D^8) S (by positivity) hS
  have hw : value w=((c:ℂ)+(s:ℂ)*I)^8 := pow8_value c s
  simp only [Nat.cast_pow] at h
  change ‖value w/(D:ℂ)^8-_‖≤_ at h
  rw [hw,←div_pow] at h
  exact h
end RHHighGaussianIntegerPower

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighChirpPairEnclosure
open RHHighChirpSeed RHHighExpEnclosure RHHighGenericExpHorner RHHighGaussianIntegerPower
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
end RHHighChirpPairEnclosure

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighChirpCache
open RHHighGenericExpHorner RHHighChirpSeed

def square (z : Int×Int) : Int×Int := (z.1*z.1-z.2*z.2,2*z.1*z.2)
def rounded8 (c s : Nat) : Int×Int :=
 let w:=square (square (square ((c:Int),(s:Int))))
 (w.1*S/(D:Int)^8,w.2*S/(D:Int)^8)
def computeCS (q : Nat) : Nat×Nat :=
 let z:=point N q D
 let v:=z^4
 let cpv:=horner (cp D) v
 let cnv:=horner (cn D) v
 let spv:=horner (sp D) v
 let snv:=horner (sn D) v
 let Q:=D^31*(31).factorial
 ((cpv-z^2*cnv)*D/Q,z*(spv-z^2*snv)*D/Q)
def reducedIndex (j : Nat) : Nat := min (j*j%(2*N)) (2*N-j*j%(2*N))

def checkOne (q : Nat) (v : Record) : Bool :=
 if needed q then
  decide (computeCS q=(v.c,v.s)) && decide (0<v.c ∧ (q=0 ∨ 0<v.s)) &&
   decide (rounded8 v.c v.s=(v.r,v.i))
 else decide (v=⟨0,0,0,0⟩)

def check : Bool := decide (expected.length=N+1) &&
 ((List.range (N+1)).zip expected).all (fun p => checkOne p.1 p.2) &&
 (List.range (2*N-1)).all (fun j => needed (reducedIndex j))
theorem checked : check=true := by decide +kernel
end RHHighChirpCache

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighChirpCache
open RHHighChirpSeed
def record (q : Nat) : Record := expected.getD q ⟨0,0,0,0⟩
lemma check_parts : expected.length=N+1 ∧
    ((List.range (N+1)).zip expected).all (fun p => checkOne p.1 p.2)=true ∧
    (List.range (2*N-1)).all (fun j => needed (reducedIndex j))=true := by
  have h := checked
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩
lemma record_checked (q : Nat) (hq : q≤N) (hn : needed q=true) :
    computeCS q=((record q).c,(record q).s) ∧
      (0<(record q).c ∧ (q=0 ∨ 0<(record q).s)) ∧
      rounded8 (record q).c (record q).s=((record q).r,(record q).i) := by
  have hl := check_parts.1
  have hidx : q<expected.length := by rw [hl];omega
  have hr : record q=expected[q] := List.getD_eq_getElem expected ⟨0,0,0,0⟩ hidx
  have hm : (q,record q)∈(List.range (N+1)).zip expected := by
    apply List.mem_iff_getElem.mpr
    refine ⟨q,by simp only [List.length_zip,List.length_range,hl];omega,?_⟩
    rw [List.getElem_zip]
    simp only [List.getElem_range,hr]
  have h := List.all_eq_true.mp check_parts.2.1 (q,record q) hm
  simp only [checkOne,hn,Bool.true_eq,if_true,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩
lemma reduced_covered (j : Nat) (hj : j<2*N-1) : needed (reducedIndex j)=true :=
  List.all_eq_true.mp check_parts.2.2 j (List.mem_range.mpr hj)
lemma reduced_le (j : Nat) : reducedIndex j≤N := by
  unfold reducedIndex
  have hr : j*j%(2*N)<2*N := Nat.mod_lt _ (by decide)
  omega
theorem half_checked : (List.range (N+1)).all
    (fun q => decide (2*point N q D≤D))=true := by decide +kernel
lemma point_half (q : Nat) (hq : q≤N) : 2*point N q D≤D := by
  have h := List.all_eq_true.mp half_checked q (List.mem_range.mpr (by omega))
  exact of_decide_eq_true h
end RHHighChirpCache

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Complex
namespace RHHighChirpCache
open RHHighExpEnclosure RHHighChirpSeed RHHighChirpPairEnclosure
noncomputable def recordValue (q : Nat) : ℂ :=
  (((record q).r:ℂ)+((record q).i:ℂ)*I)/(S:ℂ)
lemma record_enclosure (q : Nat) (hq : q≤N) (hn : needed q=true) :
    ‖recordValue q-Complex.exp (I*((Real.pi*(q:ℝ)/(N:ℝ):ℝ):ℂ))‖≤1/10^23 := by
  have hc := record_checked q hq hn
  let d := point N q D
  have hce : cosNumerator D d*D/denominator D=(record q).c :=
    congrArg Prod.fst hc.1
  have hse : sinNumerator D d*D/denominator D=(record q).s :=
    congrArg Prod.snd hc.1
  have hp : 0 < cosNumerator D d*D/denominator D := by rw [hce];exact hc.2.1.1
  have hs : d=0 ∨ 0 < sinNumerator D d*D/denominator D := by
    rcases hc.2.1.2 with hz|hs
    · left
      dsimp [d]
      rw [hz]
      simp [point]
    · right
      rw [hse]
      exact hs
  have hd := point_half q hq
  have hsmall := small_phase_error N q (by decide) hq hd hp hs
  have he : approximation D d=(((record q).c:ℂ)+((record q).s:ℂ)*I)/(D:ℂ) := by
    unfold approximation
    rw [hce,hse]
  change ‖approximation D d-Complex.exp (I*((Real.pi*(q:ℝ)/(8*(N:ℝ)):ℝ):ℂ))‖≤1/10^32 at hsmall
  rw [he] at hsmall
  let a : ℂ := (((record q).c:ℂ)+((record q).s:ℂ)*I)/(D:ℂ)
  have hpow := phase_power_error N q a (by decide) hsmall
  have hround := RHHighGaussianIntegerPower.rounded8_error (record q).c (record q).s D S
    (by decide) (by decide)
  change ‖a^8-(((rounded8 (record q).c (record q).s).1:ℂ)+
      ((rounded8 (record q).c (record q).s).2:ℂ)*I)/(S:ℂ)‖≤2/(S:ℝ) at hround
  rw [hc.2.2] at hround
  change ‖a^8-recordValue q‖≤2/(S:ℝ) at hround
  calc
    _ ≤ ‖recordValue q-a^8‖+
        ‖a^8-Complex.exp (I*((Real.pi*(q:ℝ)/(N:ℝ):ℝ):ℂ))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2/(S:ℝ)+255/10^32 := add_le_add ((norm_sub_rev _ _).trans_le hround) hpow
    _ ≤ _ := by norm_num [S]
end RHHighChirpCache

 theorem solution :
  ∀ q : Nat, q≤16384 → RHHighChirpCache.needed q=true →
  let v := RHHighChirpCache.expected.getD q ⟨0,0,0,0⟩
  ‖((v.r:ℂ)+(v.i:ℂ)*Complex.I)/(2:ℂ)^80-
    Complex.exp (Complex.I*((Real.pi*(q:ℝ)/16384:ℝ):ℂ))‖≤1/10^23 := by
  intro q hq hn
  simpa only [RHHighChirpCache.recordValue,RHHighChirpCache.record,
    RHHighChirpCache.S,RHHighChirpCache.N,Nat.cast_pow,Nat.cast_ofNat]
    using RHHighChirpCache.record_enclosure q hq hn
