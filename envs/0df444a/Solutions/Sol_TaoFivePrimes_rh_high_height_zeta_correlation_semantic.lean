-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_zeta_correlation_semantic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:27:54.967741+00:00
-- url     : https://prove2.me/submissions/6193bac4-6f12-4b00-bb92-62f47358afaa

import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Mathlib
namespace RHHighZetaCorrelationSemantic
namespace RHHighBinningSemantic
export _root_.RHHighBinningSemantic (accumulate_value add_get add_length bins_value coefficientAt coefficientAt_add pairValue sparseValue sparseValue_cons termsAux_iterates termsAux_length terms_length)
end RHHighBinningSemantic
namespace RHHighChirpCache
export _root_.RHHighChirpCache (D N Record S expected mask needed)
end RHHighChirpCache
namespace RHHighChirpIndexed
export _root_.RHHighChirpIndexed (Certificate certificate left lookup lookup_eq right tree)
end RHHighChirpIndexed
namespace RHHighDirichletBinning
export _root_.RHHighDirichletBinning (accumulate add bin bins decode decodeCoefficients field terms termsAux)
end RHHighDirichletBinning
namespace RHHighFFTArithmeticBase
export _root_.RHHighFFTArithmeticBase (bias chirp decode fieldBase raw)
end RHHighFFTArithmeticBase
namespace RHHighGlobalBinTree
export _root_.RHHighGlobalBinTree (flatten get get_sound length_flatten size valid zeroWord)
end RHHighGlobalBinTree
namespace RHHighGlobalDirichletBins
export _root_.RHHighGlobalDirichletBins (coefficient coefficient_bound coefficients_checked flatten_checked groups tree valid_checked values word word_eq)
end RHHighGlobalDirichletBins
namespace RHHighGlobalDirichletBins00
export _root_.RHHighGlobalDirichletBins00 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins00
namespace RHHighGlobalDirichletBins01
export _root_.RHHighGlobalDirichletBins01 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins01
namespace RHHighGlobalDirichletBins02
export _root_.RHHighGlobalDirichletBins02 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 row11 row12 row13 row14 row15 rows)
end RHHighGlobalDirichletBins02
namespace RHHighGlobalDirichletBins03
export _root_.RHHighGlobalDirichletBins03 (row00 row01 row02 row03 row04 row05 row06 row07 row08 row09 row10 rows)
end RHHighGlobalDirichletBins03
namespace RHHighIndexedDataTree
export _root_.RHHighIndexedDataTree (flatten get get_sound length_flatten size valid)
end RHHighIndexedDataTree
namespace RHHighPackedFFT
export _root_.RHHighPackedFFT (combine convolution decode digits output pack pair unbias windows)
end RHHighPackedFFT
namespace RHHighZetaCorrelation
export _root_.RHHighZetaCorrelation (aImag aReal bImag bReal combine convolution decode output sample signed)
end RHHighZetaCorrelation
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial
namespace RHHighPackedConvolution
lemma ofDigits_coefficients (p : Polynomial Nat) (b n : Nat) :
    Nat.ofDigits b ((List.range n).map p.coeff) =
      ∑ i ∈ Finset.range n, p.coeff i*b^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih]
    simp [Finset.sum_range_succ, Nat.mul_comm]
lemma eval_ofDigits (p : Polynomial Nat) (b n : Nat) (hn : p.natDegree<n) :
    p.eval b=Nat.ofDigits b ((List.range n).map p.coeff) := by
  rw [ofDigits_coefficients,Polynomial.eval_eq_sum_range' hn]
lemma extract_coefficient (p : Polynomial Nat) (b n i : Nat)
    (hb : 0<b) (hn : p.natDegree<n) (hi : i<n)
    (hc : ∀ j<n, p.coeff j<b) :
    p.eval b/b^i%b=p.coeff i := by
  rw [eval_ofDigits p b n hn]
  have hd : ∀ d ∈ (List.range n).map p.coeff, d<b := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨j,hj,rfl⟩
    exact hc j (List.mem_range.mp hj)
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hb _ hd,
    Nat.ofDigits_mod_eq_head!]
  have hh : (((List.range n).map p.coeff).drop i).head!=p.coeff i := by
    simp [List.head!_eq_head?_getD,List.head?_drop,List.getElem?_map,
      List.getElem?_range hi]
  rw [hh,Nat.mod_eq_of_lt (hc i hi)]
lemma packed_product_coefficient (p q : Polynomial Nat) (b n i : Nat)
    (hb : 0<b) (hn : (p*q).natDegree<n) (hi : i<n)
    (hc : ∀ j<n, (p*q).coeff j<b) :
    (p.eval b*q.eval b)/b^i%b=
      ∑ j ∈ Finset.HasAntidiagonal.antidiagonal i, p.coeff j.1*q.coeff j.2 := by
  rw [←Polynomial.eval_mul,extract_coefficient (p*q) b n i hb hn hi hc,
    Polynomial.coeff_mul]
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial Finset.HasAntidiagonal
namespace RHHighPackedConvolution
lemma vector_eval {n : Nat} (a : Fin n→Nat) (hn : 0<n) (b : Nat) :
    (Polynomial.ofFn n a).eval b=Nat.ofDigits b (List.ofFn a) := by
  rw [eval_ofDigits _ b n (Polynomial.ofFn_natDegree_lt hn a)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.length_map,List.length_range] at h₁
    simp [Polynomial.ofFn_coeff_eq_val_of_lt a h₁,h₁]
lemma vector_coeff_le {n : Nat} (a : Fin n→Nat) (A : Nat)
    (ha : ∀ j, a j≤A) (i : Nat) : (Polynomial.ofFn n a).coeff i≤A := by
  by_cases hi : i<n
  · simpa only [Polynomial.ofFn_coeff_eq_val_of_lt a hi] using ha ⟨i,hi⟩
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge a (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _
lemma vector_product_no_carry {n m : Nat} (a : Fin n→Nat) (c : Fin m→Nat)
    (A C b : Nat) (ha : ∀ j, a j≤A) (hc : ∀ j, c j≤C)
    (hb : (n+m)*A*C<b) (i : Nat) (hi : i<n+m) :
    (Polynomial.ofFn n a*Polynomial.ofFn m c).coeff i<b := by
  rw [Polynomial.coeff_mul]
  calc
    _ ≤ ∑ j ∈ antidiagonal i, A*C := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.mul_le_mul (vector_coeff_le a A ha j.1) (vector_coeff_le c C hc j.2)
    _ = (i+1)*A*C := by simp;ring
    _ ≤ (n+m)*A*C := Nat.mul_le_mul_right C (Nat.mul_le_mul_right A (by omega))
    _ < b := hb
lemma vector_product_digit {n m : Nat} (a : Fin n→Nat) (c : Fin m→Nat)
    (hn : 0<n) (hm : 0 < m) (A C b : Nat)
    (ha : ∀ j, a j≤A) (hc : ∀ j, c j≤C) (hb : (n+m)*A*C<b)
    (i : Nat) (hi : i<n+m) :
    (Nat.ofDigits b (List.ofFn a)*Nat.ofDigits b (List.ofFn c))/b^i%b=
      ∑ j ∈ antidiagonal i,
        (Polynomial.ofFn n a).coeff j.1*(Polynomial.ofFn m c).coeff j.2 := by
  have hn' := Polynomial.ofFn_natDegree_lt hn a
  have hm' := Polynomial.ofFn_natDegree_lt hm c
  have hp : (Polynomial.ofFn n a*Polynomial.ofFn m c).natDegree<n+m :=
    lt_of_le_of_lt (Polynomial.natDegree_mul_le) (by omega)
  have hb' : 0<b := by omega
  rw [←vector_eval a hn b,←vector_eval c hm b]
  exact packed_product_coefficient _ _ b (n+m) i hb' hp hi
    (fun j hj => vector_product_no_carry a c A C b ha hc hb j hj)
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighBalancedPacking
noncomputable def pair (bits : Nat) : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x::y::xs => (x+Nat.shiftLeft y bits)::pair bits xs
noncomputable def pack : Nat → Nat → List Nat → Nat
  | 0, _, xs => xs.headD 0
  | n+1, bits, xs => pack n (bits*2) (pair bits xs)
lemma pair_length (bits : Nat) (xs : List Nat) :
    (pair bits xs).length=(xs.length+1)/2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [pair]
  | singleton x => simp [pair]
  | cons_cons x y xs ih => simp only [pair,List.length_cons,ih];omega
lemma pair_digits (bits : Nat) (xs : List Nat) :
    Nat.ofDigits (2^(bits*2)) (pair bits xs)=Nat.ofDigits (2^bits) xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [pair]
  | singleton x => simp [pair,Nat.ofDigits]
  | cons_cons x y xs ih =>
    simp only [pair,Nat.ofDigits_cons]
    rw [ih]
    simp only [Nat.shiftLeft_eq',Nat.shiftLeft_eq,pow_mul]
    ring
lemma pack_eq (n bits : Nat) (xs : List Nat) (hx : xs.length≤2^n) :
    pack n bits xs=Nat.ofDigits (2^bits) xs := by
  induction n generalizing bits xs with
  | zero =>
    norm_num at hx
    cases xs with
    | nil => simp [pack,Nat.ofDigits]
    | cons x xs =>
      cases xs with
      | nil => simp [pack,Nat.ofDigits]
      | cons y ys => simp at hx
  | succ n ih =>
    rw [pack,ih]
    · exact pair_digits bits xs
    · rw [pair_length]
      rw [pow_succ] at hx
      omega
end RHHighBalancedPacking
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHHighBalancedPacking
noncomputable def digits : Nat → Nat → Nat → List Nat
  | 0, bits, p => [p &&& (Nat.shiftLeft 1 bits-1)]
  | n+1, bits, p =>
      let h:=Nat.shiftLeft bits n
      digits n bits (p &&& (Nat.shiftLeft 1 h-1))++digits n bits (Nat.shiftRight p h)
lemma digits_length (n bits p : Nat) : (digits n bits p).length=2^n := by
  induction n generalizing p with
  | zero => simp [digits]
  | succ n ih => simp [digits,List.length_append,ih,pow_succ,Nat.mul_two]
lemma low_digit (p bits n j : Nat) (hj : j<2^n) :
    (p%2^(bits*2^n))/2^(bits*j)%2^bits=p/2^(bits*j)%2^bits := by
  have hle : bits*j≤bits*2^n := Nat.mul_le_mul_left bits (by omega)
  have he : bits*j+(bits*2^n-bits*j)=bits*2^n := by omega
  rw [←he,pow_add,Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  apply Nat.pow_dvd_pow 2
  nlinarith
lemma get_digits (n bits p j : Nat) (hj : j<2^n) :
    (digits n bits p)[j]'(by rw [digits_length];exact hj)=p/2^(bits*j)%2^bits := by
  induction n generalizing p j with
  | zero =>
    have hj0 : j=0 := by norm_num at hj;omega
    subst j
    simp [digits,Nat.shiftLeft_eq',Nat.shiftLeft_eq]
  | succ n ih =>
    simp only [digits]
    have he : Nat.shiftLeft bits n=bits*2^n := Nat.shiftLeft_eq _ _
    by_cases hleft : j<2^n
    · rw [List.getElem_append_left (by rw [digits_length];exact hleft),ih _ _ hleft]
      rw [he,Nat.shiftLeft_eq',Nat.shiftLeft_eq,Nat.one_mul,Nat.and_two_pow_sub_one_eq_mod]
      exact low_digit p bits n j hleft
    · have hge : 2^n≤j := by omega
      have hr : j-2^n<2^n := by rw [pow_succ] at hj;omega
      rw [List.getElem_append_right (by rw [digits_length];exact hge)]
      simp only [digits_length]
      rw [ih _ _ hr]
      rw [he,Nat.shiftRight_eq',Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,←pow_add]
      have hex : bits*2^n+bits*(j-2^n)=bits*j := by
        rw [←Nat.mul_add,Nat.add_sub_of_le hge]
      rw [hex]
end RHHighBalancedPacking
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Finset
namespace RHHighPackedConvolution
lemma coeff_as_range {n m : Nat} (a : Fin n→Nat) (b : Fin m→Nat) (i : Nat) :
    (Polynomial.ofFn n a*Polynomial.ofFn m b).coeff i=
      ∑ j∈Finset.range (i+1), (Polynomial.ofFn n a).coeff j*(Polynomial.ofFn m b).coeff (i-j) := by
  rw [Polynomial.coeff_mul,Nat.antidiagonal_eq_map]
  simp only [Finset.sum_map]
  rfl
lemma middle_coeff {n : Nat} (hn : 0<n) (a : Fin n→Nat) (b : Fin (2*n-1)→Nat)
    (r : Nat) (hr:r<n) :
    (Polynomial.ofFn n a*Polynomial.ofFn (2*n-1) b).coeff (n-1+r)=
      ∑ j : Fin n, a j*b ⟨n-1+r-j.val,by omega⟩ := by
  rw [coeff_as_range]
  have hlen : n≤n-1+r+1 := by omega
  rw [←Finset.sum_range_add_sum_Ico _ hlen]
  have hz : (∑ j∈Finset.Ico n (n-1+r+1),
    (Polynomial.ofFn n a).coeff j*(Polynomial.ofFn (2*n-1) b).coeff (n-1+r-j))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge a (Finset.mem_Ico.mp hj).1,zero_mul]
  rw [hz,add_zero,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt b (show n-1+r-j.val<2*n-1 by omega)]
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
open Polynomial Finset
namespace RHHighPackedConvolution
lemma middle_coeff_extended {n m : Nat} (hn:0< n) (hnm:n≤ m)
    (a : Fin n→Nat) (b : Fin m→Nat) (r : Nat) (hr:r< m-n+1) :
    (Polynomial.ofFn n a*Polynomial.ofFn m b).coeff (n-1+r)=
      ∑ j:Fin n,a j*b ⟨n-1+r-j.val,by omega⟩ := by
  rw [coeff_as_range]
  have hlen:n≤ n-1+r+1:=by omega
  rw [←Finset.sum_range_add_sum_Ico _ hlen]
  have hz:(∑ j∈Finset.Ico n (n-1+r+1),
    (Polynomial.ofFn n a).coeff j*(Polynomial.ofFn m b).coeff (n-1+r-j))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge a (Finset.mem_Ico.mp hj).1,zero_mul]
  rw [hz,add_zero,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt b (show n-1+r-j.val< m by omega)]
lemma fixed_correlation (a : Fin 929→Nat) (b : Fin 1954→Nat)
    (ha:∀ j,a j≤2^142) (hb:∀ j,b j≤2^102) (r : Nat) (hr:r<1025) :
    (Nat.ofDigits (2^272) (List.ofFn a)*Nat.ofDigits (2^272) (List.ofFn b))/2^(272*(928+r))%2^272=
      ∑ j:Fin 929,a j*b ⟨928+r-j.val,by omega⟩ := by
  have h:=vector_product_digit a b (by decide) (by decide) (2^142) (2^102) (2^272)
    ha hb (by decide) (928+r) (by omega)
  rw [←Polynomial.coeff_mul] at h
  have hm:=middle_coeff_extended (n:=929) (m:=1954) (by decide) (by decide) a b r (by omega)
  have he:(2^272:Nat)^(928+r)=2^(272*(928+r)):=by rw [pow_mul]
  rw [he] at h
  exact h.trans hm
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace RHHighPackedFFT
lemma pair_length (bits : Nat) (xs : List Nat) :
    (pair bits xs).length=(xs.length+1)/2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [pair]
  | singleton x => simp [pair]
  | cons_cons x y xs ih => simp only [pair,List.length_cons,ih];omega
lemma pair_digits (bits : Nat) (xs : List Nat) :
    Nat.ofDigits (2^(bits*2)) (pair bits xs)=Nat.ofDigits (2^bits) xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [pair]
  | singleton x => simp [pair,Nat.ofDigits]
  | cons_cons x y xs ih =>
    simp only [pair,Nat.ofDigits_cons]
    rw [ih]
    simp only [Nat.shiftLeft_eq',Nat.shiftLeft_eq,pow_mul]
    ring
lemma pack_eq (n bits : Nat) (xs : List Nat) (hx : xs.length≤2^n) :
    pack n bits xs=Nat.ofDigits (2^bits) xs := by
  induction n generalizing bits xs with
  | zero =>
    norm_num at hx
    cases xs with
    | nil => simp [pack,Nat.ofDigits]
    | cons x xs =>
      cases xs with
      | nil => simp [pack,Nat.ofDigits]
      | cons y ys => simp at hx
  | succ n ih =>
    rw [pack,ih]
    · exact pair_digits bits xs
    · rw [pair_length]
      rw [pow_succ] at hx
      omega
lemma digits_length (n bits p : Nat) : (digits n bits p).length=2^n := by
  induction n generalizing p with
  | zero => simp [digits]
  | succ n ih => simp [digits,List.length_append,ih,pow_succ,Nat.mul_two]
lemma low_digit (p bits n j : Nat) (hj : j<2^n) :
    (p%2^(bits*2^n))/2^(bits*j)%2^bits=p/2^(bits*j)%2^bits := by
  have hle : bits*j≤bits*2^n := Nat.mul_le_mul_left bits (by omega)
  have he : bits*j+(bits*2^n-bits*j)=bits*2^n := by omega
  rw [←he,pow_add,Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  apply Nat.pow_dvd_pow 2
  nlinarith
lemma get_digits (n bits p j : Nat) (hj : j<2^n) :
    (digits n bits p)[j]'(by rw [digits_length];exact hj)=p/2^(bits*j)%2^bits := by
  induction n generalizing p j with
  | zero =>
    have hj0 : j=0 := by norm_num at hj;omega
    subst j
    simp [digits,Nat.shiftLeft_eq',Nat.shiftLeft_eq]
  | succ n ih =>
    simp only [digits]
    have he : Nat.shiftLeft bits n=bits*2^n := Nat.shiftLeft_eq _ _
    by_cases hleft : j<2^n
    · rw [List.getElem_append_left (by rw [digits_length];exact hleft),ih _ _ hleft]
      rw [he,Nat.shiftLeft_eq',Nat.shiftLeft_eq,Nat.one_mul,Nat.and_two_pow_sub_one_eq_mod]
      exact low_digit p bits n j hleft
    · have hge : 2^n≤j := by omega
      have hr : j-2^n<2^n := by rw [pow_succ] at hj;omega
      rw [List.getElem_append_right (by rw [digits_length];exact hge)]
      simp only [digits_length]
      rw [ih _ _ hr]
      rw [he,Nat.shiftRight_eq',Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,←pow_add]
      have hex : bits*2^n+bits*(j-2^n)=bits*j := by
        rw [←Nat.mul_add,Nat.add_sub_of_le hge]
      rw [hex]
end RHHighPackedFFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Polynomial Finset
namespace RHHighPackedConvolution
lemma list_product_digit (a b : List Nat) (A C base i : Nat)
    (ha:0<a.length) (hb:0<b.length)
    (hA:∀ x∈a,x≤A) (hC:∀ x∈b,x≤C)
    (hbase:(a.length+b.length)*A*C<base) (hi:i<a.length+b.length) :
    (Nat.ofDigits base a*Nat.ofDigits base b)/base^i%base=
      (Polynomial.ofFn a.length (fun j => a[j.val])*Polynomial.ofFn b.length (fun j => b[j.val])).coeff i := by
  let af:Fin a.length→Nat:=fun j=>a[j.val]
  let bf:Fin b.length→Nat:=fun j=>b[j.val]
  have h:=vector_product_digit af bf ha hb A C base
    (fun j => hA _ (List.getElem_mem j.isLt)) (fun j => hC _ (List.getElem_mem j.isLt)) hbase i hi
  rw [←Polynomial.coeff_mul] at h
  simpa only [af,bf,List.ofFn_getElem] using h
lemma packed_middle_digit (a b : List Nat) (na nb bits offset r : Nat)
    (ha:a.length≤2^na) (hb:b.length≤2^nb) (hr:r<2048) :
    ((RHHighPackedFFT.digits 11 bits (Nat.shiftRight
      (RHHighPackedFFT.pack na bits a*RHHighPackedFFT.pack nb bits b) (bits*offset)))[r]?).getD 0=
      (Nat.ofDigits (2^bits) a*Nat.ofDigits (2^bits) b)/2^(bits*(offset+r))%2^bits := by
  have hpack (n : Nat) (v : List Nat) (hv:v.length≤2^n) :
      RHHighPackedFFT.pack n bits v=Nat.ofDigits (2^bits) v := by
    have h:=RHHighPackedFFT.pack_eq n bits v hv
    exact h
  rw [hpack na a ha,hpack nb b hb]
  have hlen:(RHHighPackedFFT.digits 11 bits (Nat.shiftRight (Nat.ofDigits (2^bits) a*Nat.ofDigits (2^bits) b) (bits*offset))).length=2048 :=
    RHHighPackedFFT.digits_length 11 bits _
  rw [List.getElem?_eq_getElem (by rw [hlen];exact hr),Option.getD_some]
  have h:=RHHighPackedFFT.get_digits 11 bits
    (Nat.shiftRight (Nat.ofDigits (2^bits) a*Nat.ofDigits (2^bits) b) (bits*offset)) r hr
  change (RHHighPackedFFT.digits 11 bits _)[r]=_ at h
  apply h.trans
  rw [Nat.shiftRight_eq',Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,←pow_add,←Nat.mul_add]
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighPackedFFTSound
open RHHighPackedFFT
lemma window_step (b : List Nat) (N : Nat) (hN:0<N) (hlen:N<b.length) :
    (b.take N).sum-b.headD 0+(b.drop N).headD 0=(b.tail.take N).sum := by
  cases b with
  | nil => simp at hlen
  | cons x xs =>
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hN.ne'
    simp only [List.take_succ_cons,List.sum_cons,List.headD_cons,List.tail_cons,
      List.drop_succ_cons,Nat.add_sub_cancel_left]
    have hh:n<xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hlen
    rw [List.take_succ_eq_append_getElem hh,List.sum_append,List.sum_singleton]
    have he:(xs.drop n).headD 0=xs[n] := by simp [List.headD_eq_head?_getD,List.head?_drop,hh]
    rw [he]
lemma windows_eq (b : List Nat) (N L : Nat) (hN:0<N) (hlen:N+L≤b.length) :
    windows L (b.take N).sum b (b.drop N)=
      (List.range L).map (fun j => ((b.drop j).take N).sum) := by
  induction L generalizing b with
  | zero => simp [windows]
  | succ L ih =>
    have hb:b≠[] := by intro hh;simp [hh] at hlen
    have hd:b.drop N≠[] := by
      intro hh
      have h:=congrArg List.length hh
      simp only [List.length_drop,List.length_nil] at h
      omega
    cases b with
    | nil => contradiction
    | cons x xs =>
      generalize he:(x::xs).drop N=d at hd ⊢
      cases d with
      | nil => contradiction
      | cons y ys =>
        simp only [windows,List.range_succ_eq_map,List.map_cons,List.map_map,
          List.drop_zero,List.headD_cons,List.tail_cons]
        have hs : ((x::xs).take N).sum-x+y=(xs.take N).sum := by
          have h:=window_step (x::xs) N hN (by simp only [List.length_cons] at hlen ⊢;omega)
          simpa only [List.headD_cons,List.tail_cons,he] using h
        rw [hs]
        have htail : ys=xs.drop N := by
          have ht:=congrArg List.tail he
          simpa only [List.tail_drop,List.tail_cons,List.drop_succ_cons] using ht.symm
        rw [htail,ih xs (by simp only [List.length_cons] at hlen;omega)]
        rfl
end RHHighPackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
namespace RHHighPackedConvolution
lemma offset_identity {n : Nat} (a b : Fin n→Int) (A C : Int) :
    (∑ j:Fin n,(a j+A)*(b j+C))-C*(∑ j:Fin n,(a j+A))-
      A*(∑ j:Fin n,(b j+C))+(n:Int)*A*C=∑ j:Fin n,a j*b j := by
  simp only [add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hs:(∑ j:Fin n,a j*C)=∑ j:Fin n,C*a j := Finset.sum_congr rfl (fun j hj => mul_comm _ _)
  rw [hs]
  ring
lemma reverse_sum {n : Nat} (f : Fin n→Int) : (∑ j:Fin n,f j.rev)=∑ j:Fin n,f j := by
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => rfl)
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Finset
namespace RHHighPackedFFTSound
open RHHighPackedFFT
lemma windows_take_left (L sb : Nat) (xs ys : List Nat) :
    windows L sb (xs.take L) ys=windows L sb xs ys := by
  induction L generalizing sb xs ys with
  | zero => rfl
  | succ L ih =>
    cases xs with
    | nil => rfl
    | cons x xs => cases ys with
      | nil => rfl
      | cons y ys => simp only [List.take_succ_cons,windows,ih]
lemma shifted_reverse_sum (b : Fin 32767→Nat) (r : Nat) (hr:r<2048) :
    (∑ j:Fin 16384,b ⟨16383+r-j.val,by omega⟩)=
      ∑ j:Fin 16384,b ⟨r+j.val,by omega⟩ := by
  apply Fintype.sum_equiv Fin.revPerm
  intro j
  congr 1
  apply Fin.ext
  simp only [Fin.revPerm_apply,Fin.val_rev]
  omega
lemma window_as_fin_sum (b : Fin 32767→Nat) (r : Nat) (hr:r<2048) :
    (((List.ofFn b).drop r).take 16384).sum=∑ j:Fin 16384,b ⟨r+j.val,by omega⟩ := by
  have hl:(((List.ofFn b).drop r).take 16384).length=16384 := by
    simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  have he:(((List.ofFn b).drop r).take 16384)=List.ofFn (fun j:Fin 16384=>b ⟨r+j.val,by omega⟩) := by
    apply List.ext_getElem
    · simp only [hl,List.length_ofFn]
    · intro j hj hj'
      simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
  rw [he,List.sum_ofFn]
lemma offset_value {n : Nat} (a b : Fin n→Nat) (d sa sb A C : Nat)
    (hd:d=∑ j:Fin n,a j*b j) (ha:sa=∑ j:Fin n,a j) (hb:sb=∑ j:Fin n,b j) :
    (d:Int)-(C:Int)*(sa:Int)-(A:Int)*(sb:Int)+(n*A*C:Nat)=
      ∑ j:Fin n,((a j:Int)-(A:Int))*((b j:Int)-(C:Int)) := by
  have h:=RHHighPackedConvolution.offset_identity (fun j=>(a j:Int)-(A:Int))
    (fun j=>(b j:Int)-(C:Int)) (A:Int) (C:Int)
  simp only [sub_add_cancel] at h
  rw [hd,ha,hb]
  push_cast
  exact h
end RHHighPackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Finset
namespace RHHighZetaCorrelationSound
open RHHighPackedFFT RHHighPackedFFTSound
lemma reverse_sum (b : Fin 1954→Nat) (r : Nat) (hr:r<1025) :
    (∑ j:Fin 929,b ⟨928+r-j.val,by omega⟩)=(∑ j:Fin 929,b ⟨r+j.val,by omega⟩) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro j
  congr 1
  apply Fin.ext
  simp only [Fin.revPerm_apply,Fin.val_rev]
  omega
lemma window_sum (b : Fin 1954→Nat) (r : Nat) (hr:r<1025) :
    (((List.ofFn b).drop r).take 929).sum=∑ j:Fin 929,b ⟨r+j.val,by omega⟩ := by
  have hl:(((List.ofFn b).drop r).take 929).length=929 := by
    simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  have he:(((List.ofFn b).drop r).take 929)=List.ofFn (fun j:Fin 929=>b ⟨r+j.val,by omega⟩) := by
    apply List.ext_getElem
    · simp only [hl,List.length_ofFn]
    · intro j hj hj';simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
  rw [he,List.sum_ofFn]
lemma window_vector (b : Fin 1954→Nat) :
    windows 1025 ((List.ofFn b).take 929).sum ((List.ofFn b).take 1025) ((List.ofFn b).drop 929)=
      List.ofFn (fun r:Fin 1025=>∑ j:Fin 929,b ⟨r.val+j.val,by omega⟩) := by
  rw [windows_take_left,windows_eq (List.ofFn b) 929 1025 (by decide) (by simp only [List.length_ofFn];decide)]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro r hr hr'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact window_sum b r (by simpa only [List.length_ofFn] using hr')
lemma convolution_vector (a : Fin 929→Nat) (b : Fin 1954→Nat) (A C : Nat)
    (ha:∀ j,a j≤2^142) (hb:∀ j,b j≤2^102) :
    RHHighZetaCorrelation.convolution (List.ofFn a) (List.ofFn b) A C=
      List.ofFn (fun r:Fin 1025=>∑ j:Fin 929,
        ((a j:Int)-(A:Int))*((b ⟨928+r.val-j.val,by omega⟩:Int)-(C:Int))) := by
  let ds:=digits 11 272 (Nat.shiftRight (pack 10 272 (List.ofFn a)*pack 11 272 (List.ofFn b)) (272*928))
  let v:=ds.take 1025
  have hds:ds.length=2048:=digits_length 11 272 _
  have hv:v.length=1025:=by dsimp only [v];rw [List.length_take,hds];decide
  have hd (r : Nat) (hr:r<1025) :
      v[r]'(by rw [hv];exact hr)=∑ j:Fin 929,a j*b ⟨928+r-j.val,by omega⟩ := by
    have h:=RHHighPackedConvolution.packed_middle_digit (List.ofFn a) (List.ofFn b)
      10 11 272 928 r (by simp only [List.length_ofFn];decide) (by simp only [List.length_ofFn];decide) (by omega)
    change (ds[r]?).getD 0=_ at h
    rw [List.getElem?_eq_getElem (by rw [hds];omega),Option.getD_some] at h
    rw [show v[r]'(by rw [hv];exact hr)=ds[r]'(by rw [hds];omega) by exact List.getElem_take]
    exact h.trans (RHHighPackedConvolution.fixed_correlation a b ha hb r hr)
  change (v.zip (windows 1025 _ _ _)).map _=_
  rw [window_vector]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_zip,List.length_ofFn,hv,Nat.min_self]
  · intro r hr hr'
    have hr0:r<1025:=by simpa only [List.length_ofFn] using hr'
    simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
    rw [hd r hr0]
    apply offset_value a (fun j:Fin 929=>b ⟨928+r-j.val,by omega⟩)
    · rfl
    · exact List.sum_ofFn
    · exact (reverse_sum b r hr0).symm
end RHHighZetaCorrelationSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
open Complex Finset
namespace RHHighZetaCorrelationSound
open RHHighZetaCorrelation
noncomputable def sumRe (ar ai : Fin 929→Nat) (br bi : Fin 1954→Nat) (r : Fin 1025) : Int :=
  ∑ j:Fin 929,(((ar j:Int)-2^140)*((br ⟨928+r.val-j.val,by omega⟩:Int)-2^100)-
    ((ai j:Int)-2^140)*((bi ⟨928+r.val-j.val,by omega⟩:Int)-2^100))
noncomputable def sumIm (ar ai : Fin 929→Nat) (br bi : Fin 1954→Nat) (r : Fin 1025) : Int :=
  ∑ j:Fin 929,(((ar j:Int)-2^140)*((bi ⟨928+r.val-j.val,by omega⟩:Int)-2^100)+
    ((ai j:Int)-2^140)*((br ⟨928+r.val-j.val,by omega⟩:Int)-2^100))
lemma output_vector (ar ai : Fin 929→Nat) (br bi : Fin 1954→Nat)
    (hAr:∀ j,ar j≤2^141) (hAi:∀ j,ai j≤2^141)
    (hBr:∀ j,br j≤2^101) (hBi:∀ j,bi j≤2^101) :
    combine (convolution (List.ofFn ar) (List.ofFn br) (2^140) (2^100))
      (convolution (List.ofFn ai) (List.ofFn bi) (2^140) (2^100))
      (convolution (List.ofFn (fun j=>ar j+ai j)) (List.ofFn (fun j=>br j+bi j)) (2^141) (2^101))=
    List.ofFn (fun r:Fin 1025=>(sumRe ar ai br bi r,sumIm ar ai br bi r)) := by
  have hAr':∀ j,ar j≤2^142 :=fun j=>(hAr j).trans (by decide)
  have hAi':∀ j,ai j≤2^142 :=fun j=>(hAi j).trans (by decide)
  have hBr':∀ j,br j≤2^102 :=fun j=>(hBr j).trans (by decide)
  have hBi':∀ j,bi j≤2^102 :=fun j=>(hBi j).trans (by decide)
  have hAs:∀ j,ar j+ai j≤2^142 := by intro j;have hr:=hAr j;have hi:=hAi j;omega
  have hBs:∀ j,br j+bi j≤2^102 := by intro j;have hr:=hBr j;have hi:=hBi j;omega
  rw [convolution_vector ar br (2^140) (2^100) hAr' hBr',
    convolution_vector ai bi (2^140) (2^100) hAi' hBi',
    convolution_vector (fun j=>ar j+ai j) (fun j=>br j+bi j) (2^141) (2^101) hAs hBs]
  unfold combine
  apply List.ext_getElem
  · simp only [List.length_map,List.length_zip,List.length_ofFn,Nat.min_self]
  · intro r hr hr'
    have hr0:r<1025:=by simpa only [List.length_ofFn] using hr'
    simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
    have hR:(∑ j:Fin 929,((ar j:Int)-2^140)*((br ⟨928+r-j.val,by omega⟩:Int)-2^100))-
        (∑ j:Fin 929,((ai j:Int)-2^140)*((bi ⟨928+r-j.val,by omega⟩:Int)-2^100))=
        sumRe ar ai br bi ⟨r,hr0⟩ := by rw [sumRe,Finset.sum_sub_distrib]
    have hI:(∑ j:Fin 929,(((ar j+ai j:Nat):Int)-2^141)*
        (((br ⟨928+r-j.val,by omega⟩+bi ⟨928+r-j.val,by omega⟩:Nat):Int)-2^101))-
        (∑ j:Fin 929,((ar j:Int)-2^140)*((br ⟨928+r-j.val,by omega⟩:Int)-2^100))-
        (∑ j:Fin 929,((ai j:Int)-2^140)*((bi ⟨928+r-j.val,by omega⟩:Int)-2^100))=
        sumIm ar ai br bi ⟨r,hr0⟩ := by
      rw [sumIm,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [hR,hI]
end RHHighZetaCorrelationSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Finset Complex
namespace RHHighZetaCorrelationSound
open RHHighZetaCorrelation
lemma offset_eq (z : Int) (A : Nat) (hz:|z|≤(A:Int)) :
    (((z+(A:Int)).toNat:Nat):Int)-(A:Int)=z := by
  have h:=abs_le.mp hz
  omega
lemma offset_bound (z : Int) (A : Nat) (hz:|z|≤(A:Int)) :
    (z+(A:Int)).toNat≤2*A := by
  have h:=abs_le.mp hz
  omega
lemma signed_bound (v : List Nat) (j : Nat)
    (h:|(sample v j).1|≤(2:Int)^100 ∧ |(sample v j).2|≤(2:Int)^100) :
    |(signed v j).1|≤(2:Int)^100 ∧ |(signed v j).2|≤(2:Int)^100 := by
  unfold signed
  split <;> simpa only [abs_neg] using h
lemma actual_output (k : Nat) (hk:k<24) (v : List Nat)
    (hv:∀ j:Nat,j<1954 → |(sample v j).1|≤(2:Int)^100 ∧ |(sample v j).2|≤(2:Int)^100) :
    output k v=List.ofFn (fun r:Fin 1025=>
      (∑ j:Fin 929,((RHHighGlobalDirichletBins.coefficient (928-j.val) k).1*
        (signed v (928+r.val-j.val)).1-
        (RHHighGlobalDirichletBins.coefficient (928-j.val) k).2*
        (signed v (928+r.val-j.val)).2),
       ∑ j:Fin 929,((RHHighGlobalDirichletBins.coefficient (928-j.val) k).1*
        (signed v (928+r.val-j.val)).2+
        (RHHighGlobalDirichletBins.coefficient (928-j.val) k).2*
        (signed v (928+r.val-j.val)).1))) := by
  let ar:Fin 929→Nat:=fun j=>((RHHighGlobalDirichletBins.coefficient (928-j.val) k).1+(2:Int)^140).toNat
  let ai:Fin 929→Nat:=fun j=>((RHHighGlobalDirichletBins.coefficient (928-j.val) k).2+(2:Int)^140).toNat
  let br:Fin 1954→Nat:=fun j=>((signed v j.val).1+(2:Int)^100).toNat
  let bi:Fin 1954→Nat:=fun j=>((signed v j.val).2+(2:Int)^100).toNat
  have ha (j:Fin 929): |(RHHighGlobalDirichletBins.coefficient (928-j.val) k).1|≤(2:Int)^140 ∧
      |(RHHighGlobalDirichletBins.coefficient (928-j.val) k).2|≤(2:Int)^140 :=
    RHHighGlobalDirichletBins.coefficient_bound _ k (by omega) hk
  have hb (j:Fin 1954): |(signed v j.val).1|≤(2:Int)^100 ∧ |(signed v j.val).2|≤(2:Int)^100 :=
    signed_bound v j.val (hv j.val j.isLt)
  have hAr:∀ j,ar j≤2^141:=by
    intro j
    exact (offset_bound _ (2^140) (ha j).1).trans_eq (by norm_num)
  have hAi:∀ j,ai j≤2^141:=by
    intro j
    exact (offset_bound _ (2^140) (ha j).2).trans_eq (by norm_num)
  have hBr:∀ j,br j≤2^101:=by
    intro j
    exact (offset_bound _ (2^100) (hb j).1).trans_eq (by norm_num)
  have hBi:∀ j,bi j≤2^101:=by
    intro j
    exact (offset_bound _ (2^100) (hb j).2).trans_eq (by norm_num)
  have hz {N:Nat} (a b:Fin N→Nat):
      ((List.ofFn a).zip (List.ofFn b)).map (fun p=>p.1+p.2)=List.ofFn (fun j=>a j+b j) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_zip,List.length_ofFn,Nat.min_self]
    · intro j hj hj';simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
  unfold output aReal aImag bReal bImag
  change combine (convolution (List.ofFn ar) (List.ofFn br) _ _)
    (convolution (List.ofFn ai) (List.ofFn bi) _ _)
    (convolution _ _ _ _)=_
  rw [hz,hz,output_vector ar ai br bi hAr hAi hBr hBi]
  congr 1
  funext r
  apply Prod.ext <;> unfold sumRe sumIm <;> simp only [Prod.fst,Prod.snd] <;> apply Finset.sum_congr rfl <;> intro j hj
  all_goals
    simp only [ar,ai,br,bi]
    have h1:=offset_eq _ (2^140) (ha j).1
    have h2:=offset_eq _ (2^140) (ha j).2
    have h3:=offset_eq _ (2^100) (hb ⟨928+r.val-j.val,by omega⟩).1
    have h4:=offset_eq _ (2^100) (hb ⟨928+r.val-j.val,by omega⟩).2
    simp only [Nat.cast_pow,Nat.cast_ofNat] at h1 h2 h3 h4
    rw [h1,h2,h3,h4]
end RHHighZetaCorrelationSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000
namespace RHHighPackedConvolution
lemma fixed_coefficient (a : Fin 16384→Nat) (b : Fin 32767→Nat)
    (hA:∀ j,a j≤2^168) (hC:∀ j,b j≤2^83) (r : Nat) (hr:r<2048) :
    (Nat.ofDigits (2^272) (List.ofFn a)*Nat.ofDigits (2^272) (List.ofFn b))/2^(272*(16383+r))%2^272=
      ∑ j:Fin 16384,a j*b ⟨16383+r-j.val,by omega⟩ := by
  have h:=vector_product_digit a b (by decide) (by decide) (2^168) (2^83) (2^272)
    hA hC (by decide) (16383+r) (by omega)
  rw [←Polynomial.coeff_mul] at h
  have hh:=middle_coeff (n:=16384) (by decide) a b r (by omega)
  have he:(2^272:Nat)^(16383+r)=2^(272*(16383+r)) := by rw [pow_mul]
  rw [he] at h
  exact h.trans hh
end RHHighPackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Finset
namespace RHHighPackedFFTSound
open RHHighPackedFFT
lemma window_vector (b : Fin 32767→Nat) :
    windows 2048 ((List.ofFn b).take 16384).sum ((List.ofFn b).take 2048)
      ((List.ofFn b).drop 16384)=
    List.ofFn (fun r:Fin 2048=>∑ j:Fin 16384,b ⟨r.val+j.val,by omega⟩) := by
  rw [windows_take_left,windows_eq (List.ofFn b) 16384 2048 (by decide) (by simp only [List.length_ofFn];decide)]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro r hr hr'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact window_as_fin_sum b r (by simpa only [List.length_ofFn] using hr')
lemma convolution_vector (a : Fin 16384→Nat) (b : Fin 32767→Nat) (A C : Nat)
    (hA:∀ j,a j≤2^168) (hC:∀ j,b j≤2^83) :
    convolution (List.ofFn a) (List.ofFn b) A C=
      List.ofFn (fun r:Fin 2048=>∑ j:Fin 16384,
        ((a j:Int)-(A:Int))*((b ⟨16383+r.val-j.val,by omega⟩:Int)-(C:Int))) := by
  let v:=digits 11 272 (Nat.shiftRight (pack 14 272 (List.ofFn a)*pack 15 272 (List.ofFn b)) (272*16383))
  have hv:v.length=2048 := digits_length 11 272 _
  have hd (r : Nat) (hr:r<2048) :
      v[r]'(by rw [hv];exact hr)=∑ j:Fin 16384,a j*b ⟨16383+r-j.val,by omega⟩ := by
    have h:=RHHighPackedConvolution.packed_middle_digit (List.ofFn a) (List.ofFn b)
      14 15 272 16383 r (by simp only [List.length_ofFn];decide) (by simp only [List.length_ofFn];decide) hr
    change (v[r]?).getD 0=_ at h
    rw [List.getElem?_eq_getElem (by rw [hv];exact hr),Option.getD_some] at h
    exact h.trans (RHHighPackedConvolution.fixed_coefficient a b hA hC r hr)
  change (v.zip (windows 2048 _ _ _)).map _=_
  rw [window_vector]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_zip,List.length_ofFn,hv,Nat.min_self]
  · intro r hr hr'
    have hr0:r<2048 := by simpa only [List.length_ofFn] using hr'
    simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
    rw [hd r hr0]
    apply offset_value a (fun j:Fin 16384=>b ⟨16383+r-j.val,by omega⟩)
    · rfl
    · exact List.sum_ofFn
    · exact (shifted_reverse_sum b r hr0).symm
end RHHighPackedFFTSound
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
set_option maxHeartbeats 500000
open Complex
namespace RHHighPackedFFTRounding
lemma component (R : Int) (S : Nat) (hS:0<S) :
    |(R:ℝ)/(S:ℝ)^4-((R/(S:Int)^3:Int):ℝ)/(S:ℝ)|≤1/(S:ℝ) := by
  have hs:(0:ℝ)<S := by exact_mod_cast hS
  have h:=RHHighDyadicRounding.int_division_error R (S^3) (by positivity)
  have he:(R:ℝ)/(S:ℝ)^4-((R/(S:Int)^3:Int):ℝ)/(S:ℝ)=
    ((R:ℝ)/(S:ℝ)^3-((R/(S:Int)^3:Int):ℝ))/(S:ℝ) := by
    field_simp
  rw [he,abs_div,abs_of_pos hs]
  exact div_le_div_of_nonneg_right (by simpa only [Nat.cast_pow,Int.natCast_pow] using h) hs.le
lemma rounding (R J : Int) (S : Nat) (hS:0<S) :
    ‖((R:ℂ)+(J:ℂ)*I)/(S:ℂ)^4-
      (((R/(S:Int)^3:Int):ℂ)+((J/(S:Int)^3:Int):ℂ)*I)/(S:ℂ)‖≤2/(S:ℝ) := by
  have hr:=component R S hS
  have hi:=component J S hS
  have he:((R:ℂ)+(J:ℂ)*I)/(S:ℂ)^4-
      (((R/(S:Int)^3:Int):ℂ)+((J/(S:Int)^3:Int):ℂ)*I)/(S:ℂ)=
    (((R:ℝ)/(S:ℝ)^4-((R/(S:Int)^3:Int):ℝ)/(S:ℝ):ℝ):ℂ)+
      (((J:ℝ)/(S:ℝ)^4-((J/(S:Int)^3:Int):ℝ)/(S:ℝ):ℝ):ℂ)*I := by
    push_cast
    ring
  rw [he]
  have h:=norm_add_le (((R:ℝ)/(S:ℝ)^4-((R/(S:Int)^3:Int):ℝ)/(S:ℝ):ℝ):ℂ)
    ((((J:ℝ)/(S:ℝ)^4-((J/(S:Int)^3:Int):ℝ)/(S:ℝ):ℝ):ℂ)*I)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at h
  exact h.trans ((add_le_add hr hi).trans_eq (by ring))
end RHHighPackedFFTRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHHighChirpDFT
noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((Real.pi*x:ℝ)*I)
lemma phase_norm (x : ℝ) : ‖phase x‖=1 := by rw [phase,Complex.norm_exp];simp
lemma phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  unfold phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma chirp_factorization (N x y : ℝ) :
    phase (-2*x*y/N)=phase (-x^2/N)*phase (-y^2/N)*phase ((x-y)^2/N) := by
  rw [←phase_add,←phase_add]
  congr 1
  ring
noncomputable def dft {N : Nat} (a : Fin N→ℂ) (n : Fin N) : ℂ :=
  ∑ m : Fin N, a m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))
lemma dft_chirp {N : Nat} (a : Fin N→ℂ) (n : Fin N) :
    dft a n=phase (-(n.val:ℝ)^2/(N:ℝ))*
      ∑ m : Fin N, (a m*phase (-(m.val:ℝ)^2/(N:ℝ)))*
        phase (((n.val:ℝ)-(m.val:ℝ))^2/(N:ℝ)) := by
  unfold dft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show -2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ)= -2*(n.val:ℝ)*(m.val:ℝ)/(N:ℝ) by ring,
    chirp_factorization]
  ring
lemma dft_error {N : Nat} (a b : Fin N→ℂ) (ε : ℝ)
    (he : ∀ m, ‖a m-b m‖≤ε) (n : Fin N) :
    ‖dft a n-dft b n‖≤(N:ℝ)*ε := by
  unfold dft
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m : Fin N, ‖a m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))-
        b m*phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin N, ε := by
      apply Finset.sum_le_sum
      intro m hm
      rw [←sub_mul,norm_mul,phase_norm,mul_one]
      exact he m
    _ = _ := by simp
lemma product_error (a b a' b' : ℂ) (A B εa εb : ℝ)
    (hA : ‖a'‖≤A) (hB : ‖b‖≤B) (ha : ‖a-a'‖≤εa) (hb : ‖b-b'‖≤εb)
    (hεa : 0≤εa) (hεb : 0≤εb) :
    ‖a*b-a'*b'‖≤εa*B+A*εb := by
  calc
    _ = ‖(a-a')*b+a'*(b-b')‖ := by congr 1;ring
    _ ≤ ‖(a-a')*b‖+‖a'*(b-b')‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul ha hB (norm_nonneg _) hεa)
        (mul_le_mul hA hb (norm_nonneg _) (le_trans (norm_nonneg _) hA))
end RHHighChirpDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped ComplexConjugate
namespace RHHighRawChirpedInput
noncomputable def value (v : Int×Int) : ℂ := ((v.1:ℂ)+(v.2:ℂ)*I)/(2:ℂ)^80
noncomputable def product (a c : Int×Int) : Int×Int :=
  (a.1*c.1+a.2*c.2,a.2*c.1-a.1*c.2)
lemma product_value (a c : Int×Int) :
    (((product a c).1:ℂ)+((product a c).2:ℂ)*I)/(2:ℂ)^160=value a*conj (value c) := by
  unfold product value
  simp only [map_div₀,map_add,map_mul,map_pow,map_intCast,Complex.conj_I,Complex.conj_ofNat]
  push_cast
  have hs:(2:ℂ)^160=(2:ℂ)^80*(2:ℂ)^80 := by rw [←pow_add]
  rw [hs]
  field_simp
  ring_nf
  simp only [I_sq]
  ring
lemma raw_value (p k j : Nat) :
    (((RHHighFFTArithmeticBase.raw p k j).1:ℂ)+((RHHighFFTArithmeticBase.raw p k j).2:ℂ)*I)/(2:ℂ)^160=
      value (RHHighFFTArithmeticBase.decode p k)*conj (value (RHHighFFTArithmeticBase.chirp j)) := by
  exact product_value _ _
lemma input_error (f u : ℂ) (m c : Int×Int)
    (hf:‖f‖≤18) (hu:‖u‖=1) (hm:‖f-value m‖≤1/10^23) (hc:‖u-value c‖≤1/10^23) :
    ‖f*conj u-(((product m c).1:ℂ)+((product m c).2:ℂ)*I)/(2:ℂ)^160‖≤1/10^20 := by
  have hv:‖value m‖≤19 := by
    have h:=norm_sub_le_norm_sub_add_norm_sub (value m) f 0
    simp only [sub_zero,norm_sub_rev (value m) f] at h
    linarith
  rw [product_value]
  have hconj:‖conj u-conj (value c)‖≤1/10^23 := by
    rw [←map_sub,Complex.norm_conj]
    exact hc
  have h:=RHHighChirpDFT.product_error f (conj u) (value m) (conj (value c))
    19 1 (1/10^23) (1/10^23) hv (by simpa using hu.le) hm hconj (by norm_num) (by norm_num)
  exact h.trans (by norm_num)
lemma three_products (ar ai br bi : Int) :
    (((ar*br-ai*bi):Int):ℂ)+((((ar+ai)*(br+bi)-ar*br-ai*bi):Int):ℂ)*I=
      ((ar:ℂ)+(ai:ℂ)*I)*((br:ℂ)+(bi:ℂ)*I) := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring
end RHHighRawChirpedInput
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
open Complex Finset
namespace RHHighPackedFFTSound
open RHHighPackedFFT
noncomputable def sumRe (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat) (r : Fin 2048) : Int :=
  ∑ j:Fin 16384,(((ar j:Int)-2^166)*((br ⟨16383+r.val-j.val,by omega⟩:Int)-2^81)-
    ((ai j:Int)-2^166)*((bi ⟨16383+r.val-j.val,by omega⟩:Int)-2^81))
noncomputable def sumIm (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat) (r : Fin 2048) : Int :=
  ∑ j:Fin 16384,(((ar j:Int)-2^166)*((bi ⟨16383+r.val-j.val,by omega⟩:Int)-2^81)+
    ((ai j:Int)-2^166)*((br ⟨16383+r.val-j.val,by omega⟩:Int)-2^81))
lemma output_vector (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82) (c:Nat→Int×Int) :
    output (List.ofFn ar) (List.ofFn ai) (List.ofFn br) (List.ofFn bi)
      (List.ofFn (fun j=>br j+bi j)) c=
    List.ofFn (fun r:Fin 2048=>
      ((sumRe ar ai br bi r*(c r.val).1+sumIm ar ai br bi r*(c r.val).2)/(2:Int)^240,
       (sumIm ar ai br bi r*(c r.val).1-sumRe ar ai br bi r*(c r.val).2)/(2:Int)^240)) := by
  have hAr':∀ j,ar j≤2^168 :=fun j=>(hAr j).trans (by decide)
  have hAi':∀ j,ai j≤2^168 :=fun j=>(hAi j).trans (by decide)
  have hBr':∀ j,br j≤2^83 :=fun j=>(hBr j).trans (by decide)
  have hBi':∀ j,bi j≤2^83 :=fun j=>(hBi j).trans (by decide)
  have hAs:∀ j,ar j+ai j≤2^168 := by intro j;have hr:=hAr j;have hi:=hAi j;omega
  have hBs:∀ j,br j+bi j≤2^83 := by intro j;have hr:=hBr j;have hi:=hBi j;omega
  have hz:((List.ofFn ar).zip (List.ofFn ai)).map (fun p=>p.1+p.2)=List.ofFn (fun j=>ar j+ai j) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_zip,List.length_ofFn,Nat.min_self]
    · intro j hj hj';simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
  unfold output
  rw [hz,convolution_vector ar br (2^166) (2^81) hAr' hBr',
    convolution_vector ai bi (2^166) (2^81) hAi' hBi',
    convolution_vector (fun j=>ar j+ai j) (fun j=>br j+bi j) (2^167) (2^82) hAs hBs]
  unfold combine
  apply List.ext_getElem
  · simp only [List.length_map,List.length_zip,List.length_ofFn,List.length_range,Nat.min_self]
  · intro r hr hr'
    have hr0:r<2048:=by simpa only [List.length_ofFn] using hr'
    simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn,List.getElem_range]
    have hR:(∑ j:Fin 16384,((ar j:Int)-2^166)*((br ⟨16383+r-j.val,by omega⟩:Int)-2^81))-
        (∑ j:Fin 16384,((ai j:Int)-2^166)*((bi ⟨16383+r-j.val,by omega⟩:Int)-2^81))=
        sumRe ar ai br bi ⟨r,hr0⟩ := by rw [sumRe,Finset.sum_sub_distrib]
    have hI:(∑ j:Fin 16384,(((ar j+ai j:Nat):Int)-2^167)*
        (((br ⟨16383+r-j.val,by omega⟩+bi ⟨16383+r-j.val,by omega⟩:Nat):Int)-2^82))-
        (∑ j:Fin 16384,((ar j:Int)-2^166)*((br ⟨16383+r-j.val,by omega⟩:Int)-2^81))-
        (∑ j:Fin 16384,((ai j:Int)-2^166)*((bi ⟨16383+r-j.val,by omega⟩:Int)-2^81))=
        sumIm ar ai br bi ⟨r,hr0⟩ := by
      rw [sumIm,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [hR,hI]
    rfl
end RHHighPackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000
open Complex
open scoped ComplexConjugate
namespace RHHighPackedFFTSound
noncomputable def pairValue (p : Int×Int) : ℂ := ((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^80
noncomputable def roundPair (r j : Int) (c : Int×Int) : Int×Int :=
  ((r*c.1+j*c.2)/(2:Int)^240,(j*c.1-r*c.2)/(2:Int)^240)
lemma complex_rounding (r j : Int) (c : Int×Int) :
    ‖(((r:ℂ)+(j:ℂ)*I)/(2:ℂ)^240)*conj (pairValue c)-pairValue (roundPair r j c)‖≤2/(2:ℝ)^80 := by
  have h:=RHHighPackedFFTRounding.rounding (r*c.1+j*c.2) (j*c.1-r*c.2) (2^80) (by positivity)
  have he:(((r:ℂ)+(j:ℂ)*I)/(2:ℂ)^240)*conj (pairValue c)=
      ((((r*c.1+j*c.2:Int):ℂ))+(((j*c.1-r*c.2:Int):ℂ))*I)/(2:ℂ)^320 := by
    unfold pairValue
    simp only [map_div₀,map_add,map_mul,map_pow,map_intCast,Complex.conj_I,Complex.conj_ofNat]
    push_cast
    have hp:(2:ℂ)^320=(2:ℂ)^240*(2:ℂ)^80 := by rw [←pow_add]
    rw [hp]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  convert h using 1 <;> norm_num only [Nat.cast_pow,Nat.cast_ofNat,pow_mul,pairValue,roundPair]
  <;> norm_num
end RHHighPackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighPackedFFTSound
lemma gaussian_sum {N : Nat} (ar ai br bi : Fin N→Int) :
    (((∑ j:Fin N,(ar j*br j-ai j*bi j)):Int):ℂ)+
      (((∑ j:Fin N,(ar j*bi j+ai j*br j)):Int):ℂ)*I=
    ∑ j:Fin N,((ar j:ℂ)+(ai j:ℂ)*I)*((br j:ℂ)+(bi j:ℂ)*I) := by
  push_cast
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf
  simp only [I_sq]
  ring
lemma scaled_sum (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat) (r : Fin 2048) :
    (((sumRe ar ai br bi r:ℂ))+(sumIm ar ai br bi r:ℂ)*I)/(2:ℂ)^240=
    ∑ j:Fin 16384,
      (((((ar j:Int)-2^166: Int):ℂ)+(((ai j:Int)-2^166: Int):ℂ)*I)/(2:ℂ)^160)*
      (((((br ⟨16383+r.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)+
        (((bi ⟨16383+r.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)*I)/(2:ℂ)^80) := by
  unfold sumRe sumIm
  rw [gaussian_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hp:(2:ℂ)^240=(2:ℂ)^160*(2:ℂ)^80 := by rw [←pow_add]
  rw [hp]
  ring
end RHHighPackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHHighZetaCorrelationSound
open RHHighZetaCorrelation
noncomputable def complexPair (p : Int×Int) : ℂ := (p.1:ℂ)+(p.2:ℂ)*I
lemma gaussian_pair {N : Nat} (a b : Fin N→Int×Int) :
    complexPair (∑ j:Fin N,((a j).1*(b j).1-(a j).2*(b j).2),
      ∑ j:Fin N,((a j).1*(b j).2+(a j).2*(b j).1))=
    ∑ j:Fin N,complexPair (a j)*complexPair (b j) := by
  exact RHHighPackedFFTSound.gaussian_sum (fun j=>(a j).1) (fun j=>(a j).2)
    (fun j=>(b j).1) (fun j=>(b j).2)
lemma reverse_bins (k : Nat) (v : List Nat) (r : Fin 1025) :
    (∑ j:Fin 929,complexPair (RHHighGlobalDirichletBins.coefficient (928-j.val) k)*
      complexPair (signed v (928+r.val-j.val)))=
    ∑ j:Fin 929,complexPair (RHHighGlobalDirichletBins.coefficient j.val k)*
      complexPair (signed v (r.val+j.val)) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro j
  have h1:928-j.val=(Fin.revPerm j).val:=by
    simp only [Fin.revPerm_apply,Fin.val_rev]
    omega
  have h2:928+r.val-j.val=r.val+(Fin.revPerm j).val:=by
    simp only [Fin.revPerm_apply,Fin.val_rev]
    omega
  rw [h1,h2]
lemma output_complex (k : Nat) (hk:k<24) (v : List Nat)
    (hv:∀ j:Nat,j<1954 → |(sample v j).1|≤(2:Int)^100 ∧ |(sample v j).2|≤(2:Int)^100)
    (r : Fin 1025) :
    complexPair (((output k v)[r.val]?).getD (0,0))=
      ∑ j:Fin 929,complexPair (RHHighGlobalDirichletBins.coefficient j.val k)*
        complexPair (signed v (r.val+j.val)) := by
  rw [actual_output k hk v hv,List.getElem?_ofFn]
  simp only [r.isLt,dif_pos,Option.getD_some]
  exact (gaussian_pair (fun j:Fin 929=>RHHighGlobalDirichletBins.coefficient (928-j.val) k)
    (fun j:Fin 929=>signed v (928+r.val-j.val))).trans (reverse_bins k v r)
lemma output_scaled (k : Nat) (hk:k<24) (v : List Nat)
    (hv:∀ j:Nat,j<1954 → |(sample v j).1|≤(2:Int)^100 ∧ |(sample v j).2|≤(2:Int)^100)
    (r : Fin 1025) :
    complexPair (((output k v)[r.val]?).getD (0,0))/(2:ℂ)^208=
      ∑ j:Fin 929,(complexPair (RHHighGlobalDirichletBins.coefficient j.val k)/(2:ℂ)^128)*
        (complexPair (signed v (r.val+j.val))/(2:ℂ)^80) := by
  rw [output_complex k hk v hv,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hp:(2:ℂ)^208=(2:ℂ)^128*(2:ℂ)^80:=by rw [←pow_add]
  rw [hp]
  ring
end RHHighZetaCorrelationSound
end
end RHHighZetaCorrelationSemantic
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem solution (k : Nat) (hk:k<24) (v : List Nat)
 (hv:∀j:Nat,j<1954 → |(RHHighZetaCorrelation.sample v j).1|≤(2:Int)^100 ∧ |(RHHighZetaCorrelation.sample v j).2|≤(2:Int)^100)
 (r : Fin 1025) :
 RHHighBinningSemantic.pairValue (((RHHighZetaCorrelation.output k v)[r.val]?).getD (0,0))/(2:ℂ)^213=
 ∑b:Fin 929,(RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient b.val k)/(2:ℂ)^128)*
  (RHHighBinningSemantic.pairValue (RHHighZetaCorrelation.signed v (r.val+b.val))/(2:ℂ)^85) := by
 have h:=RHHighZetaCorrelationSemantic.RHHighZetaCorrelationSound.output_scaled k hk v hv r
 change RHHighBinningSemantic.pairValue (((RHHighZetaCorrelation.output k v)[r.val]?).getD (0,0))/(2:ℂ)^208=
  ∑b:Fin 929,(RHHighBinningSemantic.pairValue (RHHighGlobalDirichletBins.coefficient b.val k)/(2:ℂ)^128)*
   (RHHighBinningSemantic.pairValue (RHHighZetaCorrelation.signed v (r.val+b.val))/(2:ℂ)^80) at h
 calc
  _ = (RHHighBinningSemantic.pairValue (((RHHighZetaCorrelation.output k v)[r.val]?).getD (0,0))/(2:ℂ)^208)/32 := by
   rw[show (2:ℂ)^213=(2:ℂ)^208*32 by norm_num]
   ring
  _ = _ := by
   rw[h,Finset.sum_div]
   apply Finset.sum_congr rfl
   intro b hb
   rw[show (2:ℂ)^85=(2:ℂ)^80*32 by norm_num]
   ring
