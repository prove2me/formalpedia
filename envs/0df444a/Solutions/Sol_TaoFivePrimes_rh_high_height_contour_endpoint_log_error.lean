-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_endpoint_log_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:31:50.909337+00:00
-- url     : https://prove2.me/submissions/7328f752-b475-4244-9a18-e87a714526f5

import Definitions.Def_TaoFivePrimes_RHHighContourArithmetic
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Mathlib
namespace RHHighContourEndpointLogProof
namespace RHHighContourArithmetic
export _root_.RHHighContourArithmetic (Record check difference log16 logAux mul normSq ratio)
end RHHighContourArithmetic
namespace RHHighContourGrid
export _root_.RHHighContourGrid (cells horizontal horizontalRows jet verticalRows)
end RHHighContourGrid
namespace RHHighContourOutput00
export _root_.RHHighContourOutput00 (row00 row01 row02 row03 rows)
end RHHighContourOutput00
namespace RHHighContourOutputUpperNeg64K01
export _root_.RHHighContourOutputUpperNeg64K01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K01
namespace RHHighContourOutputUpperNeg64K02
export _root_.RHHighContourOutputUpperNeg64K02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K02
namespace RHHighContourOutputUpperNeg64K03
export _root_.RHHighContourOutputUpperNeg64K03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K03
namespace RHHighContourOutputUpperNeg64K04
export _root_.RHHighContourOutputUpperNeg64K04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K04
namespace RHHighContourOutputUpperNeg64K05
export _root_.RHHighContourOutputUpperNeg64K05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K05
namespace RHHighContourOutputUpperNeg64K06
export _root_.RHHighContourOutputUpperNeg64K06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K06
namespace RHHighContourOutputUpperNeg64K07
export _root_.RHHighContourOutputUpperNeg64K07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperNeg64K07
namespace RHHighContourOutputUpperPos64K00
export _root_.RHHighContourOutputUpperPos64K00 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K00
namespace RHHighContourOutputUpperPos64K01
export _root_.RHHighContourOutputUpperPos64K01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K01
namespace RHHighContourOutputUpperPos64K02
export _root_.RHHighContourOutputUpperPos64K02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K02
namespace RHHighContourOutputUpperPos64K03
export _root_.RHHighContourOutputUpperPos64K03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K03
namespace RHHighContourOutputUpperPos64K04
export _root_.RHHighContourOutputUpperPos64K04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K04
namespace RHHighContourOutputUpperPos64K05
export _root_.RHHighContourOutputUpperPos64K05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K05
namespace RHHighContourOutputUpperPos64K06
export _root_.RHHighContourOutputUpperPos64K06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K06
namespace RHHighContourOutputUpperPos64K07
export _root_.RHHighContourOutputUpperPos64K07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperPos64K07
namespace RHHighContourOutputUpperZeroK00
export _root_.RHHighContourOutputUpperZeroK00 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK00
namespace RHHighContourOutputUpperZeroK01
export _root_.RHHighContourOutputUpperZeroK01 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK01
namespace RHHighContourOutputUpperZeroK02
export _root_.RHHighContourOutputUpperZeroK02 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK02
namespace RHHighContourOutputUpperZeroK03
export _root_.RHHighContourOutputUpperZeroK03 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK03
namespace RHHighContourOutputUpperZeroK04
export _root_.RHHighContourOutputUpperZeroK04 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK04
namespace RHHighContourOutputUpperZeroK05
export _root_.RHHighContourOutputUpperZeroK05 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK05
namespace RHHighContourOutputUpperZeroK06
export _root_.RHHighContourOutputUpperZeroK06 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK06
namespace RHHighContourOutputUpperZeroK07
export _root_.RHHighContourOutputUpperZeroK07 (row00 row01 row02 row03 rows)
end RHHighContourOutputUpperZeroK07
namespace RHHighContourVector
export _root_.RHHighContourVector (coefficient decode raw value vector)
end RHHighContourVector
namespace RHHighVerticalJetsLeft
export _root_.RHHighVerticalJetsLeft (row00 row01 row02 rows)
end RHHighVerticalJetsLeft
namespace RHHighVerticalJetsRight
export _root_.RHHighVerticalJetsRight (row00 row01 row02 rows)
end RHHighVerticalJetsRight
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourPair
noncomputable def value (D : Nat) (p : Int×Int) : ℂ := ((p.1:ℂ)+(p.2:ℂ)*I)/(D:ℂ)
lemma normSq_cast (p : Int×Int) : (RHHighContourArithmetic.normSq p:ℝ)=(p.1:ℝ)^2+(p.2:ℝ)^2 := by
 simp only [RHHighContourArithmetic.normSq,Nat.cast_add,Nat.cast_pow,Nat.cast_natAbs,Int.cast_abs,sq_abs]
lemma norm_square (D : Nat) (p : Int×Int) :
 ‖value D p‖^2=(RHHighContourArithmetic.normSq p:ℝ)/(D:ℝ)^2 := by
 rw[value,norm_div,div_pow,Complex.norm_natCast,Complex.sq_norm]
 congr 1
 rw[normSq_cast]
 simp [Complex.normSq_apply,pow_two]
lemma lower (D L : Nat) (p : Int×Int) (hD:0<D)
    (h:L^2≤RHHighContourArithmetic.normSq p) : (L:ℝ)/D≤‖value D p‖ := by
 have hR:(L:ℝ)^2≤(RHHighContourArithmetic.normSq p:ℝ):=by exact_mod_cast h
 have he:((L:ℝ)/D)^2≤‖value D p‖^2:=by
  rw[norm_square,div_pow]
  exact div_le_div_of_nonneg_right hR (by positivity)
 nlinarith only [he,norm_nonneg (value D p),show (0:ℝ)≤(L:ℝ)/D by positivity]
lemma upper (D U : Nat) (p : Int×Int) (hD:0<D)
    (h:RHHighContourArithmetic.normSq p≤U^2) : ‖value D p‖≤(U:ℝ)/D := by
 have hR:(RHHighContourArithmetic.normSq p:ℝ)≤(U:ℝ)^2:=by exact_mod_cast h
 have he:‖value D p‖^2≤((U:ℝ)/D)^2:=by
  rw[norm_square,div_pow]
  exact div_le_div_of_nonneg_right hR (by positivity)
 nlinarith only [he,norm_nonneg (value D p),show (0:ℝ)≤(U:ℝ)/D by positivity]
end RHHighContourPair
end
section
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
end
section
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
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighDyadicComplex
noncomputable def value (D : Nat) (a : Int×Int) : ℂ := ((a.1:ℂ)+(a.2:ℂ)*I)/(D:ℂ)
noncomputable def mul (D : Nat) (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
lemma component (a : Int) (D : Nat) (hD:0<D) :
    |(a:ℝ)/(D:ℝ)^2-((a/(D:Int):Int):ℝ)/(D:ℝ)|≤1/(D:ℝ) := by
  have h:=RHHighDyadicRounding.int_division_error a D hD
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
  have hr:=RHHighDyadicRounding.int_division_error a.1 n hn
  have hi:=RHHighDyadicRounding.int_division_error a.2 n hn
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
end RHHighDyadicComplex
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHHighRoundedLog
open RHHighContourArithmetic
noncomputable def V (p : Int×Int) : ℂ := RHHighDyadicComplex.value (2^128) p
noncomputable def power (r : Int×Int) : Nat→Int×Int
 | 0 => ((2:Int)^128,0)
 | n+1 => mul (power r n) r
noncomputable def sg (n : Nat) : Int := if n%2=1 then 1 else -1
lemma V_unit : V ((2:Int)^128,0)=1 := by norm_num [V,RHHighDyadicComplex.value]
lemma V_add (a b : Int×Int) : V (a.1+b.1,a.2+b.2)=V a+V b := by
 simp only[V,RHHighDyadicComplex.value,Int.cast_add]
 ring
lemma V_signed (a : Int×Int) (j : Nat) :
 V (sg j*(a.1/(j:Int)),sg j*(a.2/(j:Int)))=(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide a j) := by
 simp only[V,RHHighDyadicComplex.value,RHHighDyadicComplex.divide,Int.cast_mul]
 ring
lemma sg_norm (j : Nat) : ‖(sg j:ℂ)‖=1 := by unfold sg;split_ifs <;> norm_num
lemma power_error (r : Int×Int) (hr:‖V r‖≤1) (n : Nat) :
 ‖V (power r n)-(V r)^n‖≤2*(n:ℝ)/(2:ℝ)^128 := by
 induction n with
 | zero => rw[power,V_unit,pow_zero,sub_self,norm_zero];norm_num
 | succ n ih =>
  have h:=RHHighDyadicComplex.mul_error (2^128) (by norm_num) (power r n) r
  change ‖V (mul (power r n) r)-V (power r n)*V r‖≤ _ at h
  have hp:‖V (power r n)*V r-(V r)^n*V r‖≤2*(n:ℝ)/(2:ℝ)^128 := by
   rw[←sub_mul,norm_mul]
   exact (mul_le_mul ih hr (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw[power,pow_succ]
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h hp)).trans_eq (by push_cast;norm_num;ring)
lemma term_error (r : Int×Int) (hr:‖V r‖≤1) (j : Nat) (hj:1 ≤ j ∧ j≤16) :
 ‖(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-
  (sg j:ℂ)*(V r)^j/(j:ℂ)‖≤34/(2:ℝ)^128 := by
 have hd:=RHHighDyadicComplex.divide_error (2^128) j (by norm_num) (by omega) (power r j)
 have hp:‖V (power r j)/(j:ℂ)-(V r)^j/(j:ℂ)‖≤2*(j:ℝ)/(2:ℝ)^128 := by
  rw[←sub_div,norm_div,Complex.norm_natCast]
  have hjR:(1:ℝ)≤ j:=by exact_mod_cast hj.1
  exact (div_le_div_of_nonneg_right (power_error r hr j) (Nat.cast_nonneg j)).trans (div_le_self (by positivity) hjR)
 have he:(sg j:ℂ)*RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-
  (sg j:ℂ)*(V r)^j/(j:ℂ)=
  (sg j:ℂ)*(RHHighDyadicComplex.value (2^128) (RHHighDyadicComplex.divide (power r j) j)-(V r)^j/(j:ℂ)):=by ring
 rw[he,norm_mul,sg_norm,one_mul]
 have hjR:(j:ℝ)≤16:=by exact_mod_cast hj.2
 exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hd hp)).trans (by norm_num; nlinarith only[hjR])
lemma power_next (r : Int×Int) (j : Nat) (hj:0< j) :
 mul (power r (j-1)) r=power r j := by
 conv_rhs => rw[←Nat.sub_add_cancel (show 1≤ j by omega)]
 rfl
lemma aux_sum (r : Int×Int) (n next : Nat) (hn:0< next) (acc : Int×Int) :
 V (logAux r n next (power r (next-1)) acc)=V acc+
  ∑j∈Finset.range n,(sg (next+j):ℂ)*RHHighDyadicComplex.value (2^128)
   (RHHighDyadicComplex.divide (power r (next+j)) (next+j)) := by
 induction n generalizing next acc with
 | zero => simp only[logAux,Finset.range_zero,Finset.sum_empty,add_zero]
 | succ n ih =>
  rw[logAux,power_next r next hn]
  have hh:=ih (next+1) (by omega)
   (acc.1+sg next*((power r next).1/(next:Int)),acc.2+sg next*((power r next).2/(next:Int)))
  simp only[Nat.add_sub_cancel] at hh
  change V (logAux r n (next+1) (power r next)
   (acc.1+sg next*((power r next).1/(next:Int)),acc.2+sg next*((power r next).2/(next:Int))))=_
  rw[hh,Finset.sum_range_succ']
  rw[V_add acc (sg next*((power r next).1/(next:Int)),sg next*((power r next).2/(next:Int))),V_signed]
  simp only[Nat.add_zero,show ∀j:Nat,next+1+j=next+(j+1) by intro j;omega]
  ring
lemma sg_power (j : Nat) : (sg j:ℂ)=(-1:ℂ)^(j+1) := by
 rw[neg_one_pow_eq_pow_mod_two]
 unfold sg
 have hj:j%2<2:=Nat.mod_lt j (by decide)
 have he:(j+1)%2=(j%2+1)%2:=by omega
 rw[he]
 generalize hq:j%2=q at hj ⊢
 interval_cases q <;> norm_num
lemma logTaylor17_eq (z : ℂ) :
 Complex.logTaylor 17 z=∑j∈Finset.range 16,(sg (1+j):ℂ)*z^(1+j)/((1+j:Nat):ℂ) := by
 rw[Complex.logTaylor,Finset.sum_range_succ']
 simp only[Nat.zero_add,pow_zero,Nat.cast_zero,div_zero,add_zero]
 apply Finset.sum_congr rfl
 intro j hj
 rw[sg_power]
 simpa only [Nat.add_comm]
lemma log16_error (r : Int×Int) (hr:‖V r‖≤1) :
 ‖V (log16 r)-Complex.logTaylor 17 (V r)‖≤1/10^30 := by
 have h:=aux_sum r 16 1 (by decide) (0,0)
 change V (log16 r)=_ at h
 have hz:V (0,0)=0:=by simp[V,RHHighDyadicComplex.value]
 rw[hz,zero_add] at h
 rw[h,logTaylor17_eq,←Finset.sum_sub_distrib]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤ ∑j∈Finset.range 16,(34/(2:ℝ)^128) := by
   exact Finset.sum_le_sum (fun j hj=> term_error r hr (1+j) ⟨by omega,by have hh:=Finset.mem_range.mp hj;omega⟩)
  _ ≤ _ :=by norm_num
end RHHighRoundedLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
open scoped ComplexConjugate
namespace RHHighContourRatioProgram
open RHHighContourArithmetic
noncomputable def pair (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
lemma normSq_pair (p : Int×Int) : (normSq p:ℂ)=pair p*conj (pair p) := by
 have hR:=RHHighContourPair.normSq_cast p
 have hC:(normSq p:ℂ)=(p.1:ℂ)^2+(p.2:ℂ)^2:=by exact_mod_cast hR
 rw[hC]
 simp only[pair,map_add,map_mul,map_intCast,Complex.conj_I]
 ring_nf
 simp only[I_sq]
 ring
lemma ratio_identity (c v : Int×Int) (hc:0< normSq c) :
 ((difference v c).1*c.1+(difference v c).2*c.2:ℂ)/ (normSq c:ℂ)+
  (((difference v c).2*c.1-(difference v c).1*c.2:ℂ)/(normSq c:ℂ))*I=
 RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1 := by
 have hM:(normSq c:ℂ)≠0:=by exact_mod_cast (Nat.ne_of_gt hc)
 have hcn:pair c≠0:=by intro h;rw[normSq_pair,h,zero_mul] at hM;exact hM rfl
 have hconj:conj (pair c)≠0 := by
  intro h
  apply hcn
  have he:=congrArg (fun z:ℂ=>conj z) h
  simpa only[starRingEnd_self_apply,map_zero] using he
 have hnum:(((difference v c).1*c.1+(difference v c).2*c.2:Int):ℂ)+
   ((((difference v c).2*c.1-(difference v c).1*c.2:Int):ℂ))*I=(pair v-pair c)*conj (pair c) := by
  simp only[difference,pair,Int.cast_add,Int.cast_sub,Int.cast_mul,map_add,map_mul,map_intCast,Complex.conj_I]
  ring_nf
  simp only[I_sq]
  ring
 have hscale (p : Int×Int) : RHHighContourPair.value (2^80) p=pair p/(2:ℂ)^80 := by
  simp only[RHHighContourPair.value,pair,Nat.cast_pow,Nat.cast_ofNat]
 have he:((normSq c:ℂ))=pair c*conj (pair c):=normSq_pair c
 calc
  _ = (((((difference v c).1*c.1+(difference v c).2*c.2:Int):ℂ)+
    ((((difference v c).2*c.1-(difference v c).1*c.2:Int):ℂ))*I)/(normSq c:ℂ)) := by push_cast;ring
  _ = (pair v-pair c)/pair c := by rw[hnum,he];field_simp [hcn,hconj] <;> ring
  _ = _ := by rw[hscale,hscale];field_simp <;> ring
lemma ratio_error (c v : Int×Int) (hc:0< normSq c) :
 ‖(RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1)-
 RHHighRoundedLog.V (ratio c v)‖≤2/(2:ℝ)^128 := by
 let a:Int:=(difference v c).1*c.1+(difference v c).2*c.2
 let b:Int:=(difference v c).2*c.1-(difference v c).1*c.2
 have h:=RHHighDyadicRounding.int_complex_rounding_error a b (normSq c) (2^128) hc (by norm_num)
 have he:((a:ℂ)+(b:ℂ)*I)/(normSq c:ℂ)=RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1 := by
  calc
   _ = (a:ℂ)/(normSq c:ℂ)+((b:ℂ)/(normSq c:ℂ))*I := by ring
   _ = _ := by simpa only[a,b,Int.cast_add,Int.cast_sub,Int.cast_mul] using ratio_identity c v hc
 rw[he] at h
 simpa only[RHHighRoundedLog.V,RHHighDyadicComplex.value,ratio,a,b,Nat.cast_pow,Nat.cast_ofNat,Int.natCast_pow] using h
end RHHighContourRatioProgram
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourLog
lemma ratio_perturbation (A B c v : ℂ)
    (hc:(1/10000:ℝ)≤‖c‖) (hA:‖A-c‖≤1/10^12) (hB:‖B-v‖≤1/10^12)
    (hr:‖v/c-1‖≤1/2) :
 ‖(B/A-1)-(v/c-1)‖≤1/10^7 ∧ ‖B/A-1‖≤3/5 := by
 have hcn:c≠0:=by intro h;rw[h,norm_zero] at hc;norm_num at hc
 have hAnorm:(1/20000:ℝ)≤‖A‖ := by
  have ht:=norm_sub_le_norm_sub_add_norm_sub c A 0
  simp only[sub_zero] at ht
  rw[norm_sub_rev] at ht
  have hs:‖A-c‖≤1/20000:=hA.trans (by norm_num)
  linarith only [ht,hc,hs]
 have hAn:A≠0:=by intro h;rw[h,norm_zero] at hAnorm;norm_num at hAnorm
 have hi:(1:ℝ)/‖A‖≤20000 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/20000) hAnorm
  norm_num at hh
  simpa only [one_div] using hh
 have hq:‖v/c‖≤3/2 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub (v/c) 1 0
  simp only[sub_zero,norm_one] at h
  linarith only[h,hr]
 have he:B/A-v/c=(B-v)/A-(v/c)*((A-c)/A) := by field_simp;ring
 have h1:‖(B-v)/A‖≤20000/10^12 := by
  rw[norm_div,div_eq_mul_inv]
  have hi':‖A‖⁻¹≤20000:=by simpa only[one_div] using hi
  exact (mul_le_mul hB hi' (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)).trans_eq (by ring)
 have h2:‖(v/c)*((A-c)/A)‖≤30000/10^12 := by
  have hi':‖A‖⁻¹≤20000:=by simpa only[one_div] using hi
  have he0:=mul_le_mul hA hi' (inv_nonneg.mpr (norm_nonneg _)) (by norm_num : (0:ℝ)≤1/10^12)
  have ht : ‖v/c‖*(‖A-c‖*‖A‖⁻¹)≤(3/2:ℝ)*((1/10^12)*20000) :=
   mul_le_mul hq he0 (by positivity) (by norm_num)
  calc
   _ = ‖v/c‖*(‖A-c‖*‖A‖⁻¹) := by simp only [norm_mul,norm_div,div_eq_mul_inv,norm_inv]
   _ ≤ (3/2:ℝ)*((1/10^12)*20000) := ht
   _ = 30000/10^12 := by norm_num
 have herr:‖(B/A-1)-(v/c-1)‖≤1/10^7 := by
  rw[show (B/A-1)-(v/c-1)=B/A-v/c by ring,he]
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (by norm_num))
 refine ⟨herr,?_⟩
 have h:=norm_sub_le_norm_sub_add_norm_sub (B/A-1) (v/c-1) 0
 simp only[sub_zero] at h
 exact h.trans ((add_le_add herr hr).trans (by norm_num))
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Set MeasureTheory
namespace RHHighContourLog
lemma right_half_slit (z : ℂ) (hz : 0 < z.re) : z∈Complex.slitPlane := by
  exact Or.inl hz
lemma segment_log_derivative (f : ℂ→ℂ) (c z v : ℂ) (hc : c≠0) (t : ℝ)
    (hf : DifferentiableAt ℂ f (z+(t:ℂ)*v))
    (hz : 0 < (f (z+(t:ℂ)*v)/c).re) :
    HasDerivAt (fun u : ℝ => Complex.log (f (z+(u:ℂ)*v)/c))
      (logDeriv f (z+(t:ℂ)*v)*v) t := by
  have ha : HasDerivAt (fun u : ℝ => z+(u:ℂ)*v) v t := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using ((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const v).const_add z
  have hb := (hf.hasDerivAt.comp t ha).div_const c
  have hl := (Complex.hasDerivAt_log (right_half_slit _ hz)).comp t hb
  have hnon : f (z+(t:ℂ)*v)≠0 := by
    intro h
    rw [h,zero_div] at hz
    norm_num at hz
  have he : (f (z+(t:ℂ)*v)/c)⁻¹*(deriv f (z+(t:ℂ)*v)*v/c)=
      logDeriv f (z+(t:ℂ)*v)*v := by
    simp only [logDeriv,Pi.div_apply]
    field_simp [hc,hnon]
  rw [he] at hl
  exact hl
lemma segment_integral (f : ℂ→ℂ) (c z v : ℂ) (hc : c≠0) (a b : ℝ)
    (hf : ∀ t∈Set.uIcc a b, DifferentiableAt ℂ f (z+(t:ℂ)*v))
    (hz : ∀ t∈Set.uIcc a b, 0 < (f (z+(t:ℂ)*v)/c).re)
    (hi : IntervalIntegrable (fun t : ℝ => logDeriv f (z+(t:ℂ)*v)*v) volume a b) :
    (∫ t : ℝ in a..b, logDeriv f (z+(t:ℂ)*v)*v)=
      Complex.log (f (z+(b:ℂ)*v)/c)-Complex.log (f (z+(a:ℂ)*v)/c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact segment_log_derivative f c z v hc t (hf t ht) (hz t ht)
  · exact hi
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighContourLog
lemma disk_half_plane (f c : ℂ) (hc : c≠0) (he : ‖f-c‖<‖c‖) : 0 < (f/c).re := by
  have hn : ‖f/c-1‖<1 := by
    have hq : f/c-1=(f-c)/c := by field_simp
    rw [hq,norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hc)).mpr he
  have hr := (Complex.abs_re_le_norm (f/c-1)).trans_lt hn
  have hh := (abs_lt.mp hr).1
  simp only [sub_re,one_re] at hh
  linarith
lemma enclosure_half_plane (f p c : ℂ) (ε r : ℝ) (hc : c≠0)
    (he : ‖f-p‖≤ε) (hp : ‖p-c‖≤r) (hmargin : ε+r<‖c‖) : 0 < (f/c).re := by
  apply disk_half_plane f c hc
  exact ((norm_sub_le_norm_sub_add_norm_sub f p c).trans (add_le_add he hp)).trans_lt hmargin
lemma log_error_near_one (z : ℂ) (hz : ‖z-1‖≤1/2) :
    ‖Complex.log z‖≤(3/2:ℝ)*‖z-1‖ := by
  have h := Complex.norm_log_one_add_half_le_self hz
  simpa only [add_sub_cancel] using h
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighContourLog
lemma log_taylor16 (z : ℂ) (hz:‖z-1‖≤1/2) :
    ‖Complex.log z-Complex.logTaylor 16 (z-1)‖≤1/500000 := by
  have h := Complex.norm_log_sub_logTaylor_le 15 (lt_of_le_of_lt hz (by norm_num : (1/2:ℝ)<1))
  simp only [add_sub_cancel,Nat.reduceAdd] at h
  norm_num only [Nat.cast_ofNat] at h
  have hp : ‖z-1‖^16≤(1/2:ℝ)^16 := pow_le_pow_left₀ (norm_nonneg _) hz _
  have hi : (1-‖z-1‖)⁻¹≤2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) (by linarith : (1/2:ℝ)≤1-‖z-1‖)
    norm_num [one_div] at hh
    exact hh
  have hinv:0≤(1-‖z-1‖)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ ‖z-1‖^16*(1-‖z-1‖)⁻¹/16 := h
    _ ≤ (1/2:ℝ)^16*2/16 := by gcongr
    _ ≤ _ := by norm_num
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighContourLog
lemma log_taylor16_three_fifths (z : ℂ) (hz:‖z-1‖≤3/5) :
 ‖Complex.log z-Complex.logTaylor 16 (z-1)‖≤1/20000 := by
 have h:=Complex.norm_log_sub_logTaylor_le 15 (lt_of_le_of_lt hz (by norm_num : (3/5:ℝ)<1))
 simp only [add_sub_cancel,Nat.reduceAdd] at h
 norm_num only [Nat.cast_ofNat] at h
 have hp:‖z-1‖^16≤(3/5:ℝ)^16:=pow_le_pow_left₀ (norm_nonneg _) hz _
 have hi:(1-‖z-1‖)⁻¹≤5/2 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2/5) (by linarith : (2/5:ℝ)≤1-‖z-1‖)
  norm_num [one_div] at hh ⊢
  exact hh
 have hinv:0≤(1-‖z-1‖)⁻¹:=inv_nonneg.mpr (by linarith)
 calc
  _ ≤‖z-1‖^16*(1-‖z-1‖)⁻¹/16:=h
  _ ≤(3/5:ℝ)^16*(5/2)/16 := by gcongr
  _ ≤_ :=by norm_num
lemma log_taylor17_three_fifths (z : ℂ) (hz:‖z-1‖≤3/5) :
 ‖Complex.log z-Complex.logTaylor 17 (z-1)‖≤1/20000 := by
 have h:=Complex.norm_log_sub_logTaylor_le 16 (lt_of_le_of_lt hz (by norm_num : (3/5:ℝ)<1))
 simp only [add_sub_cancel,Nat.reduceAdd] at h
 norm_num only [Nat.cast_ofNat] at h
 have hp:‖z-1‖^17≤(3/5:ℝ)^17:=pow_le_pow_left₀ (norm_nonneg _) hz _
 have hi:(1-‖z-1‖)⁻¹≤5/2 := by
  have hh:=one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2/5) (by linarith : (2/5:ℝ)≤1-‖z-1‖)
  norm_num [one_div] at hh ⊢
  exact hh
 have hinv:0≤(1-‖z-1‖)⁻¹:=inv_nonneg.mpr (by linarith)
 calc
  _ ≤‖z-1‖^17*(1-‖z-1‖)⁻¹/17:=h
  _ ≤(3/5:ℝ)^17*(5/2)/17 := by gcongr
  _ ≤_ :=by norm_num
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHHighContourLog
lemma power_lipschitz (z w : ℂ) (ε : ℝ) (hε:0≤ε) (hz:‖z‖≤1) (hw:‖w‖≤1)
    (he:‖z-w‖≤ε) (n : Nat) : ‖z^n-w^n‖≤(n:ℝ)*ε := by
 induction n with
 | zero => simp
 | succ n ih =>
  have hid:z^(n+1)-w^(n+1)=(z^n-w^n)*z+w^n*(z-w):=by rw[pow_succ,pow_succ];ring
  rw[hid]
  have hp:‖w^n‖≤1:=by rw[norm_pow];exact pow_le_one₀ (norm_nonneg _) hw
  have h1:‖(z^n-w^n)*z‖≤(n:ℝ)*ε:=by
   rw[norm_mul]
   exact (mul_le_mul ih hz (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2:‖w^n*(z-w)‖≤ε:=by
   rw[norm_mul]
   exact (mul_le_mul hp he (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by push_cast;ring))
lemma polynomial_lipschitz (z w : ℂ) (ε : ℝ) (hε:0≤ε) (hz:‖z‖≤1) (hw:‖w‖≤1)
    (he:‖z-w‖≤ε) (n : Nat) :
 ‖Complex.logTaylor n z-Complex.logTaylor n w‖≤(n:ℝ)*ε := by
 unfold Complex.logTaylor
 rw [←Finset.sum_sub_distrib]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤∑j∈Finset.range n,ε := by
   apply Finset.sum_le_sum
   intro j hj
   by_cases hj0:j=0
   · subst j;simp;exact hε
   · rw [←sub_div,←mul_sub,norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast]
     have hp:=power_lipschitz z w ε hε hz hw he j
     exact (div_le_div_of_nonneg_right hp (Nat.cast_nonneg j)).trans_eq (by
      have hne:(j:ℝ)≠0:=by exact_mod_cast hj0
      field_simp)
  _ =_ :=by simp
end RHHighContourLog
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHHighContourLog
lemma endpoint_log_error (c v : Int×Int) (A B : ℂ)
 (hM:0< RHHighContourArithmetic.normSq c)
 (hc:(1/10000:ℝ)≤‖RHHighContourPair.value (2^80) c‖)
 (hA:‖A-RHHighContourPair.value (2^80) c‖≤1/10^12)
 (hB:‖B-RHHighContourPair.value (2^80) v‖≤1/10^12)
 (hr:‖RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1‖≤1/2) :
 ‖Complex.log (B/A)-RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v))‖≤1/10000 := by
 let q:=RHHighContourPair.value (2^80) v/RHHighContourPair.value (2^80) c-1
 let z:=B/A-1
 let w:=RHHighRoundedLog.V (RHHighContourArithmetic.ratio c v)
 have hpert:=ratio_perturbation A B _ _ hc hA hB hr
 have hround:=RHHighContourRatioProgram.ratio_error c v hM
 have hw:‖w‖≤1 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub w q 0
  simp only[sub_zero] at h
  have hrev:‖w-q‖≤2/(2:ℝ)^128:=by rw[norm_sub_rev];exact hround
  exact h.trans ((add_le_add hrev hr).trans (by norm_num))
 have he:‖z-w‖≤1/10^7+2/(2:ℝ)^128 :=
  (norm_sub_le_norm_sub_add_norm_sub z q w).trans (add_le_add hpert.1 hround)
 have hz:‖z‖≤1:=hpert.2.trans (by norm_num)
 have hp:=polynomial_lipschitz z w (1/10^7+2/(2:ℝ)^128) (by positivity) hz hw he 17
 have ht:=log_taylor17_three_fifths (B/A) hpert.2
 have hn:=RHHighRoundedLog.log16_error (RHHighContourArithmetic.ratio c v) hw
 rw[norm_sub_rev] at hn
 have h1:=norm_sub_le_norm_sub_add_norm_sub (Complex.log (B/A)) (Complex.logTaylor 17 z)
  (RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)))
 have h2:=norm_sub_le_norm_sub_add_norm_sub (Complex.logTaylor 17 z) (Complex.logTaylor 17 w)
  (RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)))
 have hh:‖Complex.log (B/A)-RHHighRoundedLog.V (RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v))‖≤
  1/20000+17*(1/10^7+2/(2:ℝ)^128)+1/10^30 := by linarith only[h1,h2,ht,hp,hn]
 exact hh.trans (by norm_num)
end RHHighContourLog
end
end RHHighContourEndpointLogProof
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem solution (c v : Int×Int) (A B : ℂ)
 (hM:0<RHHighContourArithmetic.normSq c)
 (hc:(1/10000:ℝ)≤‖RHHighContourVector.value c‖)
 (hA:‖A-RHHighContourVector.value c‖≤1/10^12)
 (hB:‖B-RHHighContourVector.value v‖≤1/10^12)
 (hr:‖RHHighContourVector.value v/RHHighContourVector.value c-1‖≤1/2) :
 let p:=RHHighContourArithmetic.log16 (RHHighContourArithmetic.ratio c v)
 ‖Complex.log (B/A)-((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^128‖≤1/10000 := by
 have hv (p : Int×Int) : RHHighContourEndpointLogProof.RHHighContourPair.value (2^80) p=RHHighContourVector.value p := by
  simp only[RHHighContourEndpointLogProof.RHHighContourPair.value,RHHighContourVector.value,Nat.cast_pow,Nat.cast_ofNat]
 have h:=RHHighContourEndpointLogProof.RHHighContourLog.endpoint_log_error c v A B hM
  (by rw[hv];exact hc) (by rw[hv];exact hA) (by rw[hv];exact hB) (by rw[hv,hv];exact hr)
 simpa only[RHHighContourEndpointLogProof.RHHighRoundedLog.V,RHHighContourEndpointLogProof.RHHighDyadicComplex.value,Nat.cast_pow,Nat.cast_ofNat] using h
