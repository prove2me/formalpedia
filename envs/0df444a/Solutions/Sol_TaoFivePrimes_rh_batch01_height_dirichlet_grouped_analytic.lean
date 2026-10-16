-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_grouped_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:29:40.091399+00:00
-- url     : https://prove2.me/submissions/9cd92d40-8657-4666-a102-9d38ccfef42b

import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_actual_bin_semantics
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_coefficient_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_global_bin_mass
namespace RHBatch01CertifiedGroupedDirichlet
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighGlobalBinTree
export _root_.RHHighGlobalBinTree (flatten get get_sound length_flatten size valid zeroWord)
end RHHighGlobalBinTree
namespace RHBatch01GlobalDirichletBins
export _root_.RHBatch01GlobalDirichletBins (coefficient coefficient_bound coefficients_checked flatten_checked groups tree valid_checked values word word_eq)
end RHBatch01GlobalDirichletBins
namespace RHBatch01GlobalDirichletBins00
export _root_.RHBatch01GlobalDirichletBins00 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins00
namespace RHBatch01GlobalDirichletBins01
export _root_.RHBatch01GlobalDirichletBins01 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins01
namespace RHBatch01GlobalDirichletBins02
export _root_.RHBatch01GlobalDirichletBins02 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHBatch01GlobalDirichletBins02
namespace RHBatch01GlobalDirichletBins03
export _root_.RHBatch01GlobalDirichletBins03 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 rows)
end RHBatch01GlobalDirichletBins03
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHBatch01GroupedBilinear
lemma grouped {N M K : Nat} (q : Fin N→Fin M)
    (c : Fin N→Fin K→ℂ) (B F : Fin M→Fin K→ℂ)
    (hB:∀m k,B m k=∑n:Fin N,if q n=m then c n k else 0) :
    (∑m:Fin M,∑k:Fin K,B m k*F m k)=∑n:Fin N,∑k:Fin K,c n k*F (q n) k := by
  simp_rw [hB,Finset.sum_mul,ite_mul,zero_mul]
  calc
    _ = ∑k:Fin K,∑m:Fin M,∑n:Fin N,if q n=m then c n k*F m k else 0 := Finset.sum_comm
    _ = ∑k:Fin K,∑n:Fin N,∑m:Fin M,if q n=m then c n k*F m k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑n:Fin N,∑k:Fin K,∑m:Fin M,if q n=m then c n k*F m k else 0 := Finset.sum_comm
    _ = _ := by simp
lemma error {N M K : Nat} (q : Fin N→Fin M)
    (ct cp : Fin N→Fin K→ℂ) (B Ft Fp : Fin M→Fin K→ℂ)
    (εc εf A mass : ℝ) (hεc:0 ≤ εc) (hεf:0 ≤ εf) (hA:0 ≤ A)
    (hB:∀m k,B m k=∑n:Fin N,if q n=m then cp n k else 0)
    (hec:∀n k,‖ct n k-cp n k‖≤ εc)
    (hef:∀m k,‖Ft m k-Fp m k‖≤ εf)
    (hF:∀m k,‖Ft m k‖≤ A)
    (hMass:(∑m:Fin M,∑k:Fin K,‖B m k‖)≤ mass) :
    ‖(∑n:Fin N,∑k:Fin K,ct n k*Ft (q n) k)-
      (∑m:Fin M,∑k:Fin K,B m k*Fp m k)‖≤(N:ℝ)*(K:ℝ)*εc*A+mass*εf := by
  let mid:ℂ:=∑m:Fin M,∑k:Fin K,B m k*Ft m k
  have hmid:mid=∑n:Fin N,∑k:Fin K,cp n k*Ft (q n) k:=grouped q cp B Ft hB
  have hleft:‖(∑n:Fin N,∑k:Fin K,ct n k*Ft (q n) k)-mid‖≤(N:ℝ)*(K:ℝ)*εc*A := by
    rw [hmid,←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n:Fin N,∑k:Fin K,εc*A := by
        apply Finset.sum_le_sum
        intro n hn
        rw [←Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        rw [←sub_mul,norm_mul]
        exact mul_le_mul (hec n k) (hF (q n) k) (norm_nonneg _) hεc
      _ = _ := by simp;ring
  have hright:‖mid-(∑m:Fin M,∑k:Fin K,B m k*Fp m k)‖≤ mass*εf := by
    dsimp only [mid]
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑m:Fin M,∑k:Fin K,‖B m k‖*εf := by
        apply Finset.sum_le_sum
        intro m hm
        rw [←Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        rw [←mul_sub,norm_mul]
        exact mul_le_mul_of_nonneg_left (hef m k) (norm_nonneg _)
      _ = (∑m:Fin M,∑k:Fin K,‖B m k‖)*εf := by simp_rw [←Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hMass hεf
  exact (norm_sub_le_norm_sub_add_norm_sub _ mid _).trans (add_le_add hleft hright)
lemma fixed_error (a b : ℂ) (h:‖a-b‖≤(50000:ℝ)*24*(1/10^24)*65537+100*(1/10^15)) :
    ‖a-b‖≤1/10^12 := h.trans (by norm_num)
end RHBatch01GroupedBilinear
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighDirichletBinning
lemma termsAux_length (K : Nat) (d wr wi p : Int) : (termsAux K d wr wi p).length=K := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih => simp only [termsAux,List.length_cons,ih]
lemma terms_length (w : Nat) : (terms w).length=24 := termsAux_length _ _ _ _ _
lemma termsAux_iterates (K : Nat) (d wr wi p : Int) :
    termsAux K d wr wi p=(List.range K).map (fun k=>
      (wr*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128,
       wi*((fun v:Int=>v*d/(2:Int)^128)^[k] p)/(2:Int)^128)) := by
  induction K generalizing p with
  | zero => rfl
  | succ K ih =>
    rw [termsAux,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    congr 1
lemma add_length (xs ys : List (Int×Int)) : (add xs ys).length=min xs.length ys.length := by
  simp only [add,List.length_zipWith]
lemma add_get (xs ys : List (Int×Int)) (k : Nat) (hx:k<xs.length) (hy:k<ys.length) :
    (add xs ys)[k]'(by rw [add_length];omega)=(xs[k].1+ys[k].1,xs[k].2+ys[k].2) := by
  simp only [add,List.getElem_zipWith]
noncomputable def pairValue (v : Int×Int) : ℂ := (v.1:ℂ)+(v.2:ℂ)*I
noncomputable def coefficientAt (xs : List (Int×Int)) (k : Nat) : ℂ := pairValue ((xs[k]?).getD (0,0))
lemma coefficientAt_add (xs ys : List (Int×Int)) (k : Nat) (hx:k<xs.length) (hy:k<ys.length) :
    coefficientAt (add xs ys) k=coefficientAt xs k+coefficientAt ys k := by
  unfold coefficientAt
  rw [List.getElem?_eq_getElem (by rw [add_length];omega),List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy]
  simp only [Option.getD_some]
  rw [add_get xs ys k hx hy]
  unfold pairValue
  push_cast
  ring
noncomputable def sparseValue (m k : Nat) (gs : List (Nat×List (Int×Int))) : ℂ :=
  (gs.map (fun g=>if g.1=m then coefficientAt g.2 k else 0)).sum
lemma sparseValue_cons (m k j : Nat) (a : List (Int×Int)) (gs : List (Nat×List (Int×Int))) :
    sparseValue m k ((j,a)::gs)=(if j=m then coefficientAt a k else 0)+sparseValue m k gs := by
  rfl
lemma accumulate_value (m k j : Nat) (acc : List (Int×Int)) (ws : List Nat)
    (hk:k<24) (ha:acc.length=24) :
    sparseValue m k (accumulate j acc ws)=
      (if j=m then coefficientAt acc k else 0)+
      ((ws.map (fun w=>if bin w=m then coefficientAt (terms w) k else 0)).sum) := by
  induction ws generalizing j acc with
  | nil => simp [accumulate,sparseValue]
  | cons w ws ih =>
    by_cases hb:bin w=j
    · rw [accumulate,if_pos hb]
      rw [ih j (add acc (terms w)) (by rw [add_length,ha,terms_length];rfl),
        coefficientAt_add acc (terms w) k (by omega) (by rw [terms_length];exact hk)]
      simp only [List.map_cons,List.sum_cons,hb]
      by_cases hm:j=m <;> simp only [hm,if_true,if_false] <;> ring
    · rw [accumulate,if_neg hb,sparseValue_cons,ih (bin w) (terms w) (terms_length w)]
      simp only [List.map_cons,List.sum_cons]
lemma bins_value (m k : Nat) (ws : List Nat) (hk:k<24) :
    sparseValue m k (bins ws)=((ws.map (fun w=>if bin w=m then coefficientAt (terms w) k else 0)).sum) := by
  cases ws with
  | nil => rfl
  | cons w ws => exact accumulate_value m k (bin w) (terms w) ws hk (terms_length w)
end RHHighDirichletBinning
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex
namespace RHHighDirichletBinning
lemma field_shift (w k : Nat) : field (w/2^320) k=field w (k+2) := by
  unfold field
  rw [Nat.div_div_eq_div_mul]
  have he:(2:Nat)^320*2^(160*k)=2^(160*(k+2)) := by
    rw [←pow_add]
    congr 1
    omega
  rw [he]
lemma decodeCoefficients_length (K w : Nat) : (decodeCoefficients K w).length=K := by
  induction K generalizing w with
  | zero => rfl
  | succ K ih => simp only [decodeCoefficients,List.length_cons,ih]
lemma decoded_at (K w k : Nat) (hk:k<K) :
    ((decodeCoefficients K w)[k]?).getD (0,0)=(field w (2*k),field w (2*k+1)) := by
  induction K generalizing w k with
  | zero => omega
  | succ K ih =>
    cases k with
    | zero => simp only [decodeCoefficients,List.getElem?_cons_zero,Option.getD_some,Nat.mul_zero,Nat.zero_add]
    | succ k =>
      simp only [decodeCoefficients,List.getElem?_cons_succ]
      rw [ih (w/2^320) k (by omega),field_shift,field_shift]
      congr 1 <;> congr 1 <;> omega
lemma coefficientAt_decode (K w k : Nat) (hk:k<K) :
    coefficientAt (decodeCoefficients K w) k=pairValue (field w (2*k),field w (2*k+1)) := by
  rw [coefficientAt,decoded_at K w k hk]
end RHHighDirichletBinning
namespace RHBatch01GlobalDirichletBins
open RHHighDirichletBinning RHHighGlobalBinTree
theorem zero_fields_checked : (List.range 48).all (fun j=>decide (field zeroWord j=0))=true := by decide +kernel
lemma zero_fields (j : Nat) (hj:j<48) : field zeroWord j=0 :=
  of_decide_eq_true ((List.all_eq_true.mp zero_fields_checked) j (List.mem_range.mpr hj))
lemma filtered_value (xs : List Nat) (m k : Nat) (hk:k<24) :
    sparseValue m k (xs.filterMap (fun j=>if word j=zeroWord then none
      else some (j,decodeCoefficients 24 (word j))))=
    ((xs.map (fun j=>if j=m then pairValue (coefficient j k) else 0)).sum) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    by_cases hz:word j=zeroWord
    · simp only [List.filterMap_cons,if_pos hz,List.map_cons,List.sum_cons,ih]
      have he:pairValue (coefficient j k)=0 := by
        rw [coefficient,hz,zero_fields (2*k) (by omega),zero_fields (2*k+1) (by omega)]
        simp [pairValue]
      simp only [he,ite_self,zero_add]
    · simp only [List.filterMap_cons,if_neg hz,sparseValue_cons,List.map_cons,List.sum_cons,ih]
      rw [coefficientAt_decode 24 (word j) k hk]
      rfl
lemma group_value (m k : Nat) (hm:m<929) (hk:k<24) :
    sparseValue m k groups=pairValue (coefficient m k) := by
  rw [groups,filtered_value _ m k hk]
  have he:((List.range 929).map (fun j=>if j=m then pairValue (coefficient j k) else 0))=
      List.ofFn (fun j:Fin 929=>if j.val=m then pairValue (coefficient j.val k) else 0) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro j hj hj';simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  rw [he,List.sum_ofFn]
  have heq (j:Fin 929):j.val=m↔j=⟨m,hm⟩:=by simp only [Fin.ext_iff]
  simp only [heq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
end RHBatch01GlobalDirichletBins
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Complex Finset
namespace RHBatch01BinCoefficientMass
open RHHighDirichletBinning RHBatch01GlobalDirichletBins
lemma values_length : RHBatch01GlobalDirichletBins.values.length=929 := by decide +kernel
noncomputable def mass (xs : List (Int×Int)) : Nat := (xs.map (fun p=>p.1.natAbs+p.2.natAbs)).sum
lemma pair_bound (p : Int×Int) : ‖pairValue p‖≤((p.1.natAbs+p.2.natAbs:Nat):ℝ) := by
  have h:=norm_add_le (p.1:ℂ) ((p.2:ℂ)*I)
  simpa only [pairValue,norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one,Nat.cast_add,
    Nat.cast_natAbs,Int.cast_abs] using h
lemma list_bound (xs : List (Int×Int)) : ((xs.map (fun p=>‖pairValue p‖)).sum)≤(mass xs:ℝ) := by
  induction xs with
  | nil => simp [mass]
  | cons p xs ih =>
    simp only [List.map_cons,List.sum_cons,mass,Nat.cast_add] at *
    exact add_le_add (by simpa only [Nat.cast_add] using pair_bound p) ih
lemma decode_eq_ofFn (K w : Nat) : decodeCoefficients K w=
    List.ofFn (fun k:Fin K=>(field w (2*k.val),field w (2*k.val+1))) := by
  apply List.ext_getElem
  · simp only [decodeCoefficients_length,List.length_ofFn]
  · intro k hk hk'
    have hk0:k<K:=by simpa only [decodeCoefficients_length] using hk
    have h:=decoded_at K w k hk0
    rw [List.getElem?_eq_getElem hk,Option.getD_some] at h
    simpa only [List.getElem_ofFn] using h
lemma word_bound (w : Nat) :
    (∑ k:Fin 24,‖pairValue (field w (2*k.val),field w (2*k.val+1))‖)≤(mass (decodeCoefficients 24 w):ℝ) := by
  have h:=list_bound (decodeCoefficients 24 w)
  conv_lhs at h => rw [decode_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  exact h
lemma values_eq_ofFn : RHBatch01GlobalDirichletBins.values=
    List.ofFn (fun j:Fin 929=>word j.val) := by
  apply List.ext_getElem
  · simp only [values_length,List.length_ofFn]
  · intro j hj hj'
    have hj0:j<929:=by simpa only [values_length] using hj
    simp only [List.getElem_ofFn,word_eq,List.getElem?_eq_getElem hj,Option.getD_some]
lemma table_bound :
    (∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)‖)≤
    (((RHBatch01GlobalDirichletBins.values.map (fun w=>mass (decodeCoefficients 24 w))).sum:Nat):ℝ) := by
  have h:=(Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin 929)))=>word_bound (word j.val)))
  change (∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)‖)≤_ at h
  rw [values_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  push_cast
  exact h
end RHBatch01BinCoefficientMass
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Complex Finset
namespace RHBatch01BinCoefficientMass
open RHHighDirichletBinning RHBatch01GlobalDirichletBins
lemma scaled_table_bound :
    (∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)/(2:ℂ)^128‖)≤100 := by
  have h:=TaoFivePrimes.rh_batch01_height_global_bin_mass.2
  change ((RHBatch01GlobalDirichletBins.values.map (fun w=>mass (decodeCoefficients 24 w))).sum)≤100*2^128 at h
  have hR:(((RHBatch01GlobalDirichletBins.values.map (fun w=>mass (decodeCoefficients 24 w))).sum:Nat):ℝ)≤
      100*(2:ℝ)^128:=by exact_mod_cast h
  have ht: (∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)‖)≤100*(2:ℝ)^128:=
    table_bound.trans hR
  have he:(∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)/(2:ℂ)^128‖)=
      (∑ j:Fin 929,∑ k:Fin 24,‖pairValue (coefficient j.val k.val)‖)/(2:ℝ)^128 := by
    simp_rw [norm_div,norm_pow,norm_ofNat,←Finset.sum_div]
  rw [he]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [ht])
end RHBatch01BinCoefficientMass
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
namespace RHBatch01DirichletGroupedAnalytic
noncomputable def L (n : Nat) : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
noncomputable def delta (n : Nat) : ℝ := 512*L n/(2*Real.pi)-(RHBatch01DirichletArithmetic.bin n:ℝ)
noncomputable def trueCoefficient (n k : Nat) : ℂ :=
 Complex.exp (-(1/2+I*(3289999808:ℂ))*(L n:ℂ))*(delta n:ℂ)^k
noncomputable def proposed (n k : Nat) : ℂ :=
 let c:=RHBatch01DirichletArithmetic.coefficient n k
 ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128
lemma bin_bound (n : Fin 50000) : RHBatch01DirichletArithmetic.bin (n.val+1)<929 := by
 have h:=(TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure (n.val+1) 0 ⟨by omega,by omega⟩ (by decide)).2.2
 omega
noncomputable def q (n : Fin 50000) : Fin 929 := ⟨RHBatch01DirichletArithmetic.bin (n.val+1),bin_bound n⟩
lemma error (F G : Nat→Nat→ℂ)
    (hF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k‖≤65537)
    (heF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k-G m k‖≤1/10^15) :
 ‖(∑n:Fin 50000,∑k:Fin 24,trueCoefficient (n.val+1) k.val*F (RHBatch01DirichletArithmetic.bin (n.val+1)) k.val)-
   (∑m:Fin 929,∑k:Fin 24,
    (RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m.val k.val)/(2:ℂ)^128)*G m.val k.val)‖≤1/10^12 := by
 let B:Fin 929→Fin 24→ℂ:=fun m k=>RHHighBinningSemantic.pairValue
   (RHBatch01GlobalDirichletBins.coefficient m.val k.val)/(2:ℂ)^128
 have hB (m : Fin 929) (k : Fin 24) :
   B m k=∑n:Fin 50000,if q n=m then proposed (n.val+1) k.val else 0 := by
  have h:=TaoFivePrimes.rh_batch01_height_actual_bin_semantics m.val m.isLt k.val k.isLt
  dsimp only [B]
  rw [h]
  apply Finset.sum_congr rfl
  intro n hn
  have he:(q n=m) ↔ (RHBatch01DirichletArithmetic.bin (n.val+1)=m.val):=Fin.ext_iff
  simp only [he,proposed]
 have hc (n : Fin 50000) (k : Fin 24) :
   ‖trueCoefficient (n.val+1) k.val-proposed (n.val+1) k.val‖≤1/10^24 := by
  have h:=(TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure (n.val+1) k.val
    ⟨by omega,by omega⟩ k.isLt).1
  rw [norm_sub_rev]
  exact h
 have hm:(∑m:Fin 929,∑k:Fin 24,‖B m k‖)≤100 := RHBatch01BinCoefficientMass.scaled_table_bound
 have h:=RHBatch01GroupedBilinear.error q
   (fun n k=>trueCoefficient (n.val+1) k.val) (fun n k=>proposed (n.val+1) k.val) B
   (fun m k=>F m.val k.val) (fun m k=>G m.val k.val)
   (1/10^24) (1/10^15) 65537 100 (by norm_num) (by norm_num) (by norm_num)
   hB hc (fun m k=>heF m.val m.isLt k.val k.isLt) (fun m k=>hF m.val m.isLt k.val k.isLt) hm
 exact h.trans (by norm_num)
end RHBatch01DirichletGroupedAnalytic
end
end RHBatch01CertifiedGroupedDirichlet
theorem solution (F G : Nat→Nat→ℂ)
    (hF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k‖≤65537)
    (heF:∀m:Nat,m<929 → ∀k:Nat,k<24 → ‖F m k-G m k‖≤1/10^15) :
 let C:Nat→Nat→ℂ:=fun n k=>
  let L:ℝ:=Real.log (n:ℝ)+Real.log Real.pi/2
  let d:ℝ:=512*L/(2*Real.pi)-(RHBatch01DirichletArithmetic.bin n:ℝ)
  Complex.exp (-(1/2+Complex.I*(3289999808:ℂ))*(L:ℂ))*(d:ℂ)^k
 ‖(∑n:Fin 50000,∑k:Fin 24,C (n.val+1) k.val*F (RHBatch01DirichletArithmetic.bin (n.val+1)) k.val)-
   (∑m:Fin 929,∑k:Fin 24,
    (RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m.val k.val)/(2:ℂ)^128)*G m.val k.val)‖≤1/10^12 := by
 exact RHBatch01CertifiedGroupedDirichlet.RHBatch01DirichletGroupedAnalytic.error F G hF heF
#print axioms solution
