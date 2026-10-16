-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_complex_ball_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:48:47.26814+00:00
-- url     : https://prove2.me/submissions/eab621bb-84d1-440d-8eaf-2f84e91a3a34

import Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHFastBallFullRounding
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
end RHFastBallFullRounding
namespace RHFastBallFullPointArithmetic
noncomputable def value (D : Nat) (a : Int×Int) : ℂ := ((a.1:ℂ)+(a.2:ℂ)*I)/(D:ℂ)
noncomputable def mul (D : Nat) (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
lemma component (a : Int) (D : Nat) (hD:0<D) :
    |(a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)|≤1/(D:ℝ) := by
  have h:=RHFastBallFullRounding.int_division_error a D hD
  have hd:(0:ℝ)<D:=by exact_mod_cast hD
  rw [show (a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)=
    ((a:ℝ)/D-((a/(D:Int):Int):ℝ))/(D:ℝ) by ring,
    abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right h hd.le
lemma mul_error (D : Nat) (hD:0<D) (a b : Int×Int) :
    ‖value D (mul D a b)-value D a*value D b‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  have hr:=component (a.1*b.1-a.2*b.2) D hD
  have hi:=component (a.1*b.2+a.2*b.1) D hD
  have he:value D a*value D b-value D (mul D a b)=
      ((((a.1*b.1-a.2*b.2:Int):ℝ)/(D:ℝ)^2-(((a.1*b.1-a.2*b.2)/(D:Int):Int):ℝ)/(D:ℝ):ℝ):ℂ)+
      ((((a.1*b.2+a.2*b.1:Int):ℝ)/(D:ℝ)^2-(((a.1*b.2+a.2*b.1)/(D:Int):Int):ℝ)/(D:ℝ):ℝ):ℂ)*I := by
    unfold value mul
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact (add_le_add hr hi).trans_eq (by ring)
lemma divide_error (D n : Nat) (hD:0<D) (hn:0<n) (a : Int×Int) :
    ‖value D (divide a n)-value D a/(n:ℂ)‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  have hr:=RHFastBallFullRounding.int_division_error a.1 n hn
  have hi:=RHFastBallFullRounding.int_division_error a.2 n hn
  have hd:(0:ℝ)<D:=by exact_mod_cast hD
  have he:value D a/(n:ℂ)-value D (divide a n)=
    ((((a.1:ℝ)/(n:ℝ)-((a.1/(n:Int):Int):ℝ))/(D:ℝ):ℝ):ℂ)+
    ((((a.2:ℝ)/(n:ℝ)-((a.2/(n:Int):Int):ℝ))/(D:ℝ):ℝ):ℂ)*I := by
    unfold value divide
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
    abs_div,abs_of_pos hd]
  exact (add_le_add (div_le_div_of_nonneg_right hr hd.le)
    (div_le_div_of_nonneg_right hi hd.le)).trans_eq (by ring)
end RHFastBallFullPointArithmetic

namespace RHFastBallFullPrimitives
open RHFastBallArithmetic RHFastBallSemantics
lemma nat_div_upper (N D:Nat) (hD:0<D) :
 (N:ℝ)/(D:ℝ)≤((N/D:Nat):ℝ)+1 := by
 have hd:(0:ℝ)<D:=by exact_mod_cast hD
 have hr:(N%D:Nat)<D:=Nat.mod_lt N hD
 have he:(N/D:Nat)*D+N%D=N:=by simpa only [Nat.mul_comm] using Nat.div_add_mod N D
 have her:((N/D:Nat):ℝ)*(D:ℝ)+(N%D:Nat)=N:=by exact_mod_cast he
 have hrr:((N%D:Nat):ℝ)<D:=by exact_mod_cast hr
 apply (div_le_iff₀ hd).mpr
 nlinarith
lemma value_norm (D:Nat) (hD:0<D) (a:Ball) :
 ‖value D a‖≤(magnitude a:ℝ)/(D:ℝ) := by
 rw [value,norm_div,Complex.norm_natCast]
 apply div_le_div_of_nonneg_right _ (by positivity)
 calc
  _ ≤ ‖(a.re:ℂ)‖+‖(a.im:ℂ)*I‖:=norm_add_le _ _
  _ = (magnitude a:ℝ):=by
   rw [norm_mul,norm_I,mul_one,←norm_natAbs a.re,←norm_natAbs a.im]
   simp only [Complex.norm_natCast,magnitude,Nat.cast_add]
lemma value_add (D:Nat) (a b:Ball) : value D (add a b)=value D a+value D b := by
 unfold value add
 push_cast
 ring
lemma value_neg (D:Nat) (a:Ball) : value D (neg a)= -value D a := by
 unfold value neg
 push_cast
 ring
lemma add_sound (D:Nat) (a b:Ball) (x y:ℂ)
 (hx:encloses D a x) (hy:encloses D b y) : encloses D (add a b) (x+y) := by
 unfold encloses at hx hy ⊢
 rw [value_add]
 have he:x+y-(value D a+value D b)=(x-value D a)+(y-value D b):=by ring
 rw [he]
 apply (norm_add_le _ _).trans
 convert add_le_add hx hy using 1 <;> simp only [add,Nat.cast_add] <;> ring
lemma neg_sound (D:Nat) (a:Ball) (x:ℂ) (hx:encloses D a x) : encloses D (neg a) (-x) := by
 unfold encloses at hx ⊢
 rw [value_neg,show -x- -value D a= -(x-value D a) by ring,norm_neg]
 exact hx
lemma mul_sound (D:Nat) (hD:0<D) (a b:Ball) (x y:ℂ)
 (hx:encloses D a x) (hy:encloses D b y) : encloses D (mul D a b) (x*y) := by
 have hd:(0:ℝ)<D:=by exact_mod_cast hD
 have ha:=value_norm D hD a
 have hb:=value_norm D hD b
 unfold encloses at hx hy ⊢
 let N:=magnitude a*b.radius+magnitude b*a.radius+a.radius*b.radius
 have hc:‖value D a*value D b-value D (mul D a b)‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  simpa only [value,mul,RHFastBallFullPointArithmetic.value,RHFastBallFullPointArithmetic.mul]
   using RHFastBallFullPointArithmetic.mul_error D hD (a.re,a.im) (b.re,b.im)
 have hid:x*y-value D a*value D b=
  (x-value D a)*value D b+value D a*(y-value D b)+(x-value D a)*(y-value D b):=by ring
 have he:‖x*y-value D a*value D b‖≤(N:ℝ)/(D:ℝ)^2 := by
  rw [hid]
  apply norm_add₃_le.trans
  simp only [norm_mul]
  calc
   _ ≤ ((a.radius:ℝ)/D)*((magnitude b:ℝ)/D)+
     ((magnitude a:ℝ)/D)*((b.radius:ℝ)/D)+((a.radius:ℝ)/D)*((b.radius:ℝ)/D):=by gcongr
   _ = _ := by dsimp only [N];push_cast;field_simp <;> ring
 have htotal:=norm_sub_le_norm_sub_add_norm_sub (x*y) (value D a*value D b) (value D (mul D a b))
 apply htotal.trans
 apply (add_le_add he hc).trans
 change (N:ℝ)/(D:ℝ)^2+2/(D:ℝ)≤((3+N/D:Nat):ℝ)/(D:ℝ)
 push_cast
 calc
  _ = ((N:ℝ)/(D:ℝ)+2)/(D:ℝ) := by field_simp <;> ring
  _ ≤ _ := by
   apply div_le_div_of_nonneg_right _ hd.le
   linarith [nat_div_upper N D hD]

lemma self_sound (D:Nat) (a:Ball) : encloses D a (value D a) := by
 unfold encloses
 simp only [sub_self,norm_zero]
 positivity
lemma integer_sound (D:Nat) (hD:0<D) (n:Int) : encloses D (integer D n) (n:ℂ) := by
 have hd:(D:ℂ)≠0:=by exact_mod_cast hD.ne'
 have hv:value D (integer D n)=(n:ℂ):=by
  unfold value integer
  push_cast
  field_simp [hd] <;> ring
 unfold encloses
 rw [hv]
 simp [integer]
lemma rational_sound (D:Nat) (hD:0<D) (p:Int) (q:Nat) (hq:0<q) :
 encloses D (rational D p q) ((p:ℂ)/(q:ℂ)) := by
 have h:=RHFastBallFullRounding.int_scaled_rounding_error p q D hq hD
 have he:(p:ℂ)/(q:ℂ)-value D (rational D p q)=
  (((p:ℝ)/(q:ℝ)-((p*(D:Int)/(q:Int):Int):ℝ)/(D:ℝ):ℝ):ℂ) := by
  unfold value rational
  push_cast
  ring
 unfold encloses
 rw [he,Complex.norm_real,Real.norm_eq_abs]
 simpa only [rational,Nat.cast_one] using h
lemma divide_sound (D:Nat) (hD:0<D) (a:Ball) (x:ℂ) (n:Nat) (hn:0<n)
 (hx:encloses D a x) : encloses D (divide a n) (x/(n:ℂ)) := by
 have hd:(0:ℝ)<D:=by exact_mod_cast hD
 have hnr:(0:ℝ)<n:=by exact_mod_cast hn
 unfold encloses at hx ⊢
 have hc:‖value D a/(n:ℂ)-value D (divide a n)‖≤2/(D:ℝ) := by
  rw [norm_sub_rev]
  simpa only [value,divide,RHFastBallFullPointArithmetic.value,RHFastBallFullPointArithmetic.divide]
   using RHFastBallFullPointArithmetic.divide_error D n hD hn (a.re,a.im)
 have hi:‖x/(n:ℂ)-value D a/(n:ℂ)‖≤((a.radius:ℝ)/(D:ℝ))/(n:ℝ) := by
  rw [←sub_div,norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hx hnr.le
 have htri:=norm_sub_le_norm_sub_add_norm_sub (x/(n:ℂ)) (value D a/(n:ℂ)) (value D (divide a n))
 apply htri.trans
 apply (add_le_add hi hc).trans
 change ((a.radius:ℝ)/(D:ℝ))/(n:ℝ)+2/(D:ℝ)≤((3+a.radius/n:Nat):ℝ)/(D:ℝ)
 push_cast
 calc
  _ = ((a.radius:ℝ)/(n:ℝ)+2)/(D:ℝ) := by ring
  _ ≤ _ := by
   apply div_le_div_of_nonneg_right _ hd.le
   linarith [nat_div_upper a.radius n hn]
lemma scale_sound (D:Nat) (a:Ball) (x:ℂ) (n:Int) (hx:encloses D a x) :
 encloses D (scale a n) ((n:ℂ)*x) := by
 have hv:value D (scale a n)=(n:ℂ)*value D a:=by
  unfold value scale
  push_cast
  ring
 unfold encloses at hx ⊢
 rw [hv,←mul_sub,norm_mul]
 have hn:‖(n:ℂ)‖=(n.natAbs:ℝ):=by rw [←norm_natAbs n,Complex.norm_natCast]
 rw [hn]
 convert! mul_le_mul_of_nonneg_left hx (by positivity:(0:ℝ)≤n.natAbs) using 1 <;>
  simp only [scale,Nat.cast_mul] <;> ring
lemma inflate_sound (D:Nat) (hD:0<D) (a:Ball) (x:ℂ) (n:Nat) (hx:encloses D a x) :
 encloses D (inflate a n) x := by
 unfold encloses at hx ⊢
 change ‖x-value D a‖≤((a.radius+n:Nat):ℝ)/(D:ℝ)
 apply hx.trans
 apply div_le_div_of_nonneg_right _ (by positivity)
 exact_mod_cast (Nat.le_add_right a.radius n)
lemma value_rotate (D:Nat) (a:Ball) (n:Nat) :
 value D (rotate a n)=(-I)^(n%4)*value D a := by
 unfold rotate
 have hn:n%4<4:=Nat.mod_lt n (by decide)
 generalize hm:n%4=j at hn ⊢
 interval_cases j <;> norm_num [value,pow_succ] <;> push_cast <;> ring_nf <;>
  simp only [I_sq] <;> ring
lemma rotate_radius (a:Ball) (n:Nat) : (rotate a n).radius=a.radius := by
 unfold rotate
 split_ifs <;> rfl
lemma rotate_sound (D:Nat) (a:Ball) (x:ℂ) (n:Nat) (hx:encloses D a x) :
 encloses D (rotate a n) ((-I)^(n%4)*x) := by
 unfold encloses at hx ⊢
 rw [value_rotate,rotate_radius,←mul_sub,norm_mul]
 simpa only [norm_pow,norm_neg,norm_I,one_pow,one_mul] using hx
lemma power_sound (D:Nat) (hD:0<D) (a:Ball) (x:ℂ) (n:Nat) (hx:encloses D a x) :
 encloses D (power D a n) (x^n) := by
 induction n with
 | zero=>simpa only [power,pow_zero,Int.cast_one] using integer_sound D hD 1
 | succ n ih=>simpa only [power,pow_succ] using mul_sound D hD (power D a n) a (x^n) x ih hx
end RHFastBallFullPrimitives

theorem solution (D:Nat) (hD:0<D) : RHFastBallInterface.Sound D :=
 {self_mem:=RHFastBallFullPrimitives.self_sound D
  integer_mem:=RHFastBallFullPrimitives.integer_sound D hD
  rational_mem:=RHFastBallFullPrimitives.rational_sound D hD
  add_mem:=RHFastBallFullPrimitives.add_sound D
  neg_mem:=RHFastBallFullPrimitives.neg_sound D
  sub_mem:=by
   intro a b x y hx hy
   simpa only [RHFastBallArithmetic.sub,sub_eq_add_neg] using
    RHFastBallFullPrimitives.add_sound D a (RHFastBallArithmetic.neg b) x (-y) hx
     (RHFastBallFullPrimitives.neg_sound D b y hy)
  mul_mem:=RHFastBallFullPrimitives.mul_sound D hD
  divide_mem:=RHFastBallFullPrimitives.divide_sound D hD
  scale_mem:=RHFastBallFullPrimitives.scale_sound D
  rotate_mem:=RHFastBallFullPrimitives.rotate_sound D
  inflate_mem:=RHFastBallFullPrimitives.inflate_sound D hD
  power_mem:=RHFastBallFullPrimitives.power_sound D hD}
#print axioms solution
