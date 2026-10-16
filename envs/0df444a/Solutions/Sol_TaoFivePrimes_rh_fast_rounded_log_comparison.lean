-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_rounded_log_comparison
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:35:34.437323+00:00
-- url     : https://prove2.me/submissions/4a4357fa-d0f0-4ec7-9cbc-385a91019eb5

import Definitions.Def_TaoFivePrimes_RHFastRoundedLogArithmetic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHFastRoundedLogProof
noncomputable def approximate : List Nat → Nat → Nat → Nat → Nat → Nat
  | [],_,_,_,_ => 0
  | c::cs,x,y,F,D => c*D/F+x*approximate cs x y F D/y
noncomputable def exactValue : List Nat → Nat → Nat → Nat → Nat → ℚ
  | [],_,_,_,_ => 0
  | c::cs,x,y,F,D => (c:ℚ)*D/F+(x:ℚ)/y*exactValue cs x y F D
lemma floor_error (a d : Nat) (hd:0<d) :
    0≤(a:ℚ)/d-(a/d:Nat) ∧ (a:ℚ)/d-(a/d:Nat)<1 := by
  have hdQ:(0:ℚ)<d:=by exact_mod_cast hd
  have hm:((a%d:Nat):ℚ)<d:=by exact_mod_cast Nat.mod_lt a hd
  have he:(a:ℚ)=((a%d:Nat):ℚ)+(d:ℚ)*(a/d:Nat):=by exact_mod_cast (Nat.mod_add_div a d).symm
  constructor
  · apply (sub_nonneg.mpr ((le_div_iff₀ hdQ).mpr ?_))
    nlinarith [show (0:ℚ)≤(a%d:Nat) by positivity]
  · rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ hdQ).mpr
    nlinarith
lemma approximation_error (cs : List Nat) (x y F D : Nat)
    (hy:0<y) (hF:0<F) (hxy:x≤y) :
    0≤exactValue cs x y F D-(approximate cs x y F D:ℚ) ∧
    exactValue cs x y F D-(approximate cs x y F D:ℚ)≤2*cs.length := by
  have hyQ:(0:ℚ)<y:=by exact_mod_cast hy
  have hxyQ:(x:ℚ)≤y:=by exact_mod_cast hxy
  have hxQ:(0:ℚ)≤(x:ℚ)/y:=div_nonneg (by positivity) hyQ.le
  have hr:(x:ℚ)/y≤1:=(div_le_one hyQ).mpr hxyQ
  induction cs with
  | nil => simp [exactValue,approximate]
  | cons c cs ih =>
    have hc:=floor_error (c*D) F hF
    have hv:=floor_error (x*approximate cs x y F D) y hy
    push_cast at hc hv
    have hlo:=mul_nonneg hxQ ih.1
    have hhi:((x:ℚ)/y)*(exactValue cs x y F D-(approximate cs x y F D:ℚ))≤2*cs.length:=
      (mul_le_mul_of_nonneg_left ih.2 hxQ).trans (by nlinarith [show (0:ℚ)≤cs.length by positivity])
    simp only [exactValue,approximate,Nat.cast_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    have he:((x:ℚ)*(approximate cs x y F D:ℚ))/y=
      ((x:ℚ)/y)*(approximate cs x y F D:ℚ):=by ring
    rw [he] at hv
    constructor <;> nlinarith
lemma exact_homogeneous (cs : List Nat) (x y F D : Nat) (hy:0<y) (hF:0<F) :
 exactValue cs x y F D=
  (D:ℚ)*y*(RHFastKernelHomogeneousHorner.hom cs x y:ℚ)/((F:ℚ)*(y:ℚ)^cs.length) := by
 have hyQ:(y:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hy)
 have hFQ:(F:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hF)
 induction cs with
 | nil => simp [exactValue,RHFastKernelHomogeneousHorner.hom]
 | cons c cs ih =>
  simp only [exactValue,RHFastKernelHomogeneousHorner.hom,List.length_cons,
   Nat.cast_add,Nat.cast_mul,Nat.cast_pow,ih]
  field_simp [hyQ,hFQ]
  <;> ring
lemma log_exact (p q D : Nat) (hq:0<q) :
 (RHFastKernelLogData.numerator p q:ℚ)*D/(RHFastKernelLogData.denominator q:ℚ)=
  (2*(p:ℚ)/q)*exactValue RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D := by
 rw [exact_homogeneous _ _ _ _ _ (by positivity) (by decide +kernel)]
 have hlen:RHFastKernelLogData.coefficients.length=40:=by decide +kernel
 rw [hlen]
 have hqQ:(q:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hq)
 simp only [RHFastKernelLogData.numerator,RHFastKernelLogData.denominator,
   Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
 field_simp [hqQ,RHFastKernelLogData.F]
 <;> ring
noncomputable def roundedFast (p q D : Nat) : Nat :=
 2*p*approximate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D/q
lemma log_rounding_error (p q D : Nat) (hq:0<q) (hp:2*p≤q) :
 |(RHFastKernelLogData.rounded p q D:ℚ)-(roundedFast p q D:ℚ)|≤81 := by
 have hqQ:(0:ℚ)<q:=by exact_mod_cast hq
 have hpQ:2*(p:ℚ)≤q:=by exact_mod_cast hp
 have hρ0:0≤2*(p:ℚ)/q:=by positivity
 have hρ1:2*(p:ℚ)/q≤1:=(div_le_one hqQ).mpr hpQ
 have hxy:p^2≤q^2:=Nat.pow_le_pow_left (by omega) 2
 have hc:=approximation_error RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D (by positivity) (by decide +kernel) hxy
 have hlen:RHFastKernelLogData.coefficients.length=40:=by decide +kernel
 rw [hlen] at hc
 norm_num only [Nat.cast_ofNat] at hc
 have ho:=floor_error (RHFastKernelLogData.numerator p q*D) (RHFastKernelLogData.denominator q) (by
  unfold RHFastKernelLogData.denominator RHFastKernelLogData.F;positivity)
 have hn:=floor_error (2*p*approximate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D) q hq
 simp only [Nat.cast_mul,Nat.cast_ofNat] at ho hn
 rw [log_exact p q D hq] at ho
 change 0≤_-(RHFastKernelLogData.rounded p q D:ℚ) ∧ _-(RHFastKernelLogData.rounded p q D:ℚ)<1 at ho
 have he:(2*(p:ℚ)*(approximate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D:ℚ))/q=
   (2*(p:ℚ)/q)*(approximate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D:ℚ):=by ring
 rw [he] at hn
 change 0≤_-(roundedFast p q D:ℚ) ∧ _-(roundedFast p q D:ℚ)<1 at hn
 have hlo:=mul_nonneg hρ0 hc.1
 have hhi: (2*(p:ℚ)/q)*(exactValue RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D-
   (approximate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D:ℚ))≤80:=
  (mul_le_mul_of_nonneg_left hc.2 hρ0).trans (by linarith)
 exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
end RHFastRoundedLogProof

lemma RHFastRoundedLogProof.evaluate_eq (cs : List Nat) (x y F D : Nat) :
 RHFastRoundedLogArithmetic.evaluate cs x y F D=RHFastRoundedLogProof.approximate cs x y F D := by
 induction cs with
 | nil => rfl
 | cons c cs ih => simp only [RHFastRoundedLogArithmetic.evaluate,RHFastRoundedLogProof.approximate,ih]
theorem solution (p q D : Nat) (hq:0<q) (hp:2*p≤q) :
 |(RHFastKernelLogData.rounded p q D:ℚ)-(RHFastRoundedLogArithmetic.rounded p q D:ℚ)|≤81 := by
 have he : RHFastRoundedLogArithmetic.rounded p q D=RHFastRoundedLogProof.roundedFast p q D := by
  unfold RHFastRoundedLogArithmetic.rounded RHFastRoundedLogProof.roundedFast
  rw [RHFastRoundedLogProof.evaluate_eq]
 rw [he]
 exact RHFastRoundedLogProof.log_rounding_error p q D hq hp
#print axioms solution
