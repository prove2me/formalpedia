-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_fft_uniform_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:25:52.14842+00:00
-- url     : https://prove2.me/submissions/3dff285e-ebe9-4fd0-91de-3943616ab215

import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Theorems.Thm_TaoFivePrimes_rh_high_height_chirp_enclosures_16384
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_moment_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
namespace RHFastKernelUniformGammaFFT
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial Finset.HasAntidiagonal
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHBatch01BalancedPacking
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
end RHBatch01BalancedPacking
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHBatch01BalancedPacking
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
end RHBatch01BalancedPacking
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Finset
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
namespace RHHighPackedFFT
open _root_.RHHighPackedFFT
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
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01PackedFFTSound
open _root_.RHHighPackedFFT
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
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
namespace RHBatch01PackedConvolution
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
end RHBatch01PackedConvolution
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Finset
namespace RHBatch01PackedFFTSound
open _root_.RHHighPackedFFT
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
  have h:=RHBatch01PackedConvolution.offset_identity (fun j=>(a j:Int)-(A:Int))
    (fun j=>(b j:Int)-(C:Int)) (A:Int) (C:Int)
  simp only [sub_add_cancel] at h
  rw [hd,ha,hb]
  push_cast
  exact h
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Finset
namespace RHBatch01PackedFFTSound
open _root_.RHHighPackedFFT
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
    have h:=RHBatch01PackedConvolution.packed_middle_digit (List.ofFn a) (List.ofFn b)
      14 15 272 16383 r (by simp only [List.length_ofFn];decide) (by simp only [List.length_ofFn];decide) hr
    change (v[r]?).getD 0=_ at h
    rw [List.getElem?_eq_getElem (by rw [hv];exact hr),Option.getD_some] at h
    exact h.trans (RHBatch01PackedConvolution.fixed_coefficient a b hA hC r hr)
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
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHBatch01DyadicRounding
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
end RHBatch01DyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHBatch01DyadicRounding
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
end RHBatch01DyadicRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHBatch01PackedFFTRounding
lemma component (R : Int) (S : Nat) (hS:0<S) :
    |(R:ℝ)/(S:ℝ)^4-((R/(S:Int)^3:Int):ℝ)/(S:ℝ)|≤1/(S:ℝ) := by
  have hs:(0:ℝ)<S := by exact_mod_cast hS
  have h:=RHBatch01DyadicRounding.int_division_error R (S^3) (by positivity)
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
end RHBatch01PackedFFTRounding
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex
namespace RHBatch01ChirpDFT
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
end RHBatch01ChirpDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
open scoped ComplexConjugate
namespace RHBatch01RawChirpedInput
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
  have h:=RHBatch01ChirpDFT.product_error f (conj u) (value m) (conj (value c))
    19 1 (1/10^23) (1/10^23) hv (by simpa using hu.le) hm hconj (by norm_num) (by norm_num)
  exact h.trans (by norm_num)
lemma three_products (ar ai br bi : Int) :
    (((ar*br-ai*bi):Int):ℂ)+((((ar+ai)*(br+bi)-ar*br-ai*bi):Int):ℂ)*I=
      ((ar:ℂ)+(ai:ℂ)*I)*((br:ℂ)+(bi:ℂ)*I) := by
  push_cast
  ring_nf
  simp only [I_sq]
  ring
end RHBatch01RawChirpedInput
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
open Complex Finset
namespace RHBatch01PackedFFTSound
open _root_.RHHighPackedFFT
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
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000
open Complex
open scoped ComplexConjugate
namespace RHBatch01PackedFFTSound
noncomputable def pairValue (p : Int×Int) : ℂ := ((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^80
noncomputable def roundPair (r j : Int) (c : Int×Int) : Int×Int :=
  ((r*c.1+j*c.2)/(2:Int)^240,(j*c.1-r*c.2)/(2:Int)^240)
lemma complex_rounding (r j : Int) (c : Int×Int) :
    ‖(((r:ℂ)+(j:ℂ)*I)/(2:ℂ)^240)*conj (pairValue c)-pairValue (roundPair r j c)‖≤2/(2:ℝ)^80 := by
  have h:=RHBatch01PackedFFTRounding.rounding (r*c.1+j*c.2) (j*c.1-r*c.2) (2^80) (by positivity)
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
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
namespace RHBatch01PackedFFTSound
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
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHBatch01ChirpDFT
lemma four_product_error (a b c d ap bp cp dp : ℂ) (ε : ℝ)
    (hε:0≤ε ∧ ε≤1) (ha:‖a‖≤18) (hb:‖b‖=1) (hc:‖c‖=1) (hd:‖d‖=1)
    (hea:‖a-ap‖≤ε) (heb:‖b-bp‖≤ε) (hec:‖c-cp‖≤ε) (hed:‖d-dp‖≤ε) :
    ‖a*b*c*d-ap*bp*cp*dp‖≤134*ε := by
  have hap:‖ap‖≤19 := by
    have h:=norm_sub_le_norm_sub_add_norm_sub ap a 0
    simp only [sub_zero,norm_sub_rev ap a] at h
    linarith
  have hbp:‖bp‖≤2 := by
    have h:=norm_sub_le_norm_sub_add_norm_sub bp b 0
    simp only [sub_zero,norm_sub_rev bp b,hb] at h
    linarith
  have hcp:‖cp‖≤2 := by
    have h:=norm_sub_le_norm_sub_add_norm_sub cp c 0
    simp only [sub_zero,norm_sub_rev cp c,hc] at h
    linarith
  have h1:‖a*b-ap*bp‖≤20*ε := by
    have h:=product_error a b ap bp 19 1 ε ε hap hb.le hea heb hε.1 hε.1
    nlinarith
  have hnorm2:‖ap*bp‖≤38 := by
    rw [norm_mul]
    exact (mul_le_mul hap hbp (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h2:‖a*b*c-ap*bp*cp‖≤58*ε := by
    have h:=product_error (a*b) c (ap*bp) cp 38 1 (20*ε) ε hnorm2 hc.le h1 hec (mul_nonneg (by norm_num) hε.1) hε.1
    nlinarith
  have hnorm3:‖ap*bp*cp‖≤76 := by
    rw [norm_mul]
    exact (mul_le_mul hnorm2 hcp (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h3:=product_error (a*b*c) d (ap*bp*cp) dp 76 1 (58*ε) ε hnorm3 hd.le h2 hed (mul_nonneg (by norm_num) hε.1) hε.1
  nlinarith
lemma dft_chirp_error {N : Nat} (a ap : Fin N→ℂ) (b bp : Fin N→ℂ)
    (c cp : Fin N→Fin N→ℂ) (ε : ℝ) (hε:0≤ε ∧ ε≤1)
    (ha:∀ m,‖a m‖≤18) (hb:∀ m,b m=phase (-(m.val:ℝ)^2/(N:ℝ)))
    (hc:∀ n m,c n m=phase (((n.val:ℝ)-(m.val:ℝ))^2/(N:ℝ)))
    (hea:∀ m,‖a m-ap m‖≤ε) (heb:∀ m,‖b m-bp m‖≤ε)
    (hec:∀ n m,‖c n m-cp n m‖≤ε) (n : Fin N) :
    ‖dft a n-bp n*(∑ m:Fin N,ap m*bp m*cp n m)‖≤(N:ℝ)*134*ε := by
  have he:dft a n-bp n*(∑ m:Fin N,ap m*bp m*cp n m)=
      ∑ m:Fin N,(a m*b m*c n m*b n-ap m*bp m*cp n m*bp n) := by
    rw [dft_chirp,←hb n,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hb m,hc n m]
    ring
  rw [he]
  calc
    _ ≤ ∑ m:Fin N,‖a m*b m*c n m*b n-ap m*bp m*cp n m*bp n‖ := norm_sum_le _ _
    _ ≤ ∑ m:Fin N,134*ε := by
      apply Finset.sum_le_sum
      intro m hm
      exact four_product_error (a m) (b m) (c n m) (b n) (ap m) (bp m) (cp n m) (bp n) ε hε
        (ha m) (by rw [hb,phase_norm]) (by rw [hc,phase_norm]) (by rw [hb,phase_norm])
        (hea m) (heb m) (hec n m) (heb n)
    _ = _ := by simp;ring
end RHBatch01ChirpDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology
namespace RHBatch01Fourier
noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2*Real.pi*x:ℝ)*Complex.I)
lemma fourier_scale (f : ℝ → ℂ) (B : ℝ) (hB : 0<B) (w : ℝ) :
    𝓕 (fun x : ℝ => f (B*x)) w=(B⁻¹:ℂ)*𝓕 f (w/B) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  have hi : (∫ x : ℝ, Complex.exp (((-2*Real.pi*x*w:ℝ):ℂ)*I) • f (B*x))=
      ∫ x : ℝ, (fun y : ℝ => Complex.exp (((-2*Real.pi*y*(w/B):ℝ):ℂ)*I) • f y) (B*x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    congr 3
    field_simp
  rw [hi]
  convert! Measure.integral_comp_mul_left (fun y : ℝ =>
    Complex.exp (((-2*Real.pi*y*(w/B):ℝ):ℂ)*I) • f y) B using 1 <;>
    simp [abs_of_pos (inv_pos.mpr hB),Complex.real_smul,smul_eq_mul]
lemma scaled_poisson (f : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0<B) (x : ℝ) :
    (∑' k : ℤ, f (x+(k:ℝ)*B))=
      (B⁻¹:ℂ)*∑' k : ℤ, 𝓕 (f:ℝ→ℂ) ((k:ℝ)/B)*phase ((k:ℝ)*x/B) := by
  let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ B hB.ne').toContinuousLinearEquiv
  let g : 𝓢(ℝ,ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (y : ℝ) : g y=f (B*y) := rfl
  have h := g.tsum_eq_tsum_fourier (x/B)
  change (∑' k : ℤ, g (x/B+(k:ℝ)))=
    ∑' k : ℤ, 𝓕 (g:ℝ→ℂ) (k:ℝ)*fourier k ((x/B:ℝ):UnitAddCircle) at h
  have hl (k : ℤ) : g (x/B+(k:ℝ))=f (x+(k:ℝ)*B) := by
    rw [hg]
    congr 1
    field_simp [hB.ne'] <;> ring
  have hr (k : ℤ) : 𝓕 (g:ℝ→ℂ) (k:ℝ)=
      (B⁻¹:ℂ)*𝓕 (f:ℝ→ℂ) ((k:ℝ)/B) := fourier_scale _ B hB (k:ℝ)
  have hp (k : ℤ) : fourier k ((x/B:ℝ):UnitAddCircle)=phase ((k:ℝ)*x/B) := by
    rw [fourier_coe_apply]
    unfold phase
    congr 1
    push_cast
    ring
  simp_rw [hl,hr,hp,mul_assoc] at h
  rw [tsum_mul_left] at h
  exact h
lemma phase_norm (x : ℝ) : ‖phase x‖=1 := by
  rw [phase,Complex.norm_exp]
  simp
lemma phase_add_int (x : ℝ) (k : Int) : phase (x+(k:ℝ))=phase x := by
  have he : ((2*Real.pi*(x+(k:ℝ)):ℝ):ℂ)*I=
      ((2*Real.pi*x:ℝ):ℂ)*I+(k:ℂ)*(2*(Real.pi:ℂ)*I) := by push_cast;ring
  rw [phase,he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
  rfl
lemma split_integer_tsum {N : Nat} [NeZero N] (H : Int → ℂ) (hH : Summable H) :
    (∑' k : Int, H k)=∑ m : Fin N, ∑' q : Int, H (q*(N:Int)+(m.val:Int)) := by
  let e : Fin N × Int ≃ Int := (Equiv.prodComm (Fin N) Int).trans (Int.divModEquiv N).symm
  have he (m : Fin N) (q : Int) : e (m,q)=q*(N:Int)+(m.val:Int) := rfl
  have hs := hH.comp_injective e.injective
  rw [←e.tsum_eq H]
  change (∑' c : Fin N × Int, (H ∘ e) c)=_
  rw [hs.tsum_prod,tsum_fintype]
  simp only [Function.comp_def,he]
lemma poisson_dft_pair {N : Nat} [NeZero N] (f : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0<B)
    (hf : Summable (fun k : Int => ‖𝓕 (f:ℝ→ℂ) ((k:ℝ)/B)‖)) (n : Int) :
    (∑' q : Int, f ((n:ℝ)*B/(N:ℝ)+(q:ℝ)*B))=
      (B⁻¹:ℂ)*∑ m : Fin N,
        (∑' q : Int, 𝓕 (f:ℝ→ℂ) (((q*(N:Int)+(m.val:Int)):ℝ)/B))*
          phase ((m.val:ℝ)*(n:ℝ)/(N:ℝ)) := by
  rw [scaled_poisson f B hB]
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  have hc (k : Int) : (k:ℝ)*((n:ℝ)*B/(N:ℝ))/B=(k:ℝ)*(n:ℝ)/(N:ℝ) := by field_simp <;> ring
  simp_rw [hc]
  let H : Int → ℂ := fun k => 𝓕 (f:ℝ→ℂ) ((k:ℝ)/B)*phase ((k:ℝ)*(n:ℝ)/(N:ℝ))
  have hH : Summable H := by
    apply Summable.of_norm_bounded hf
    intro k
    simp only [H,norm_mul,phase_norm,mul_one,le_refl]
  rw [split_integer_tsum (N:=N) H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hp (q : Int) : phase ((((q*(N:Int)+(m.val:Int)):Int):ℝ)*(n:ℝ)/(N:ℝ))=
      phase ((m.val:ℝ)*(n:ℝ)/(N:ℝ)) := by
    have he : (((q*(N:Int)+(m.val:Int)):Int):ℝ)*(n:ℝ)/(N:ℝ)=
        (m.val:ℝ)*(n:ℝ)/(N:ℝ)+((q*n:Int):ℝ) := by push_cast;field_simp;ring
    rw [he,phase_add_int]
  simp only [H]
  simp_rw [hp]
  rw [tsum_mul_right]
  congr 1
  apply tsum_congr
  intro q
  push_cast
  rfl
end RHBatch01Fourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHBatch01GenericDFT
variable {N : Nat} [NeZero N]
noncomputable def e : Fin N ≃ ZMod N := (ZMod.finEquiv N).toEquiv
noncomputable def lift (a : Fin N→ℂ) : ZMod N→ℂ := fun j => a (e.symm j)
lemma val_e (m : Fin N) : (e m).val=m.val := by
  cases N with
  | zero => exact Fin.elim0 m
  | succ n => rfl
lemma character (m n : Fin N) :
    ZMod.stdAddChar (N:=N) (-(e m*e n):ZMod N)=RHBatch01ChirpDFT.phase (-2*(m.val:ℝ)*(n.val:ℝ)/(N:ℝ)) := by
  have hm : (m.val:ZMod N)=e m := by rw [←val_e m];exact ZMod.natCast_zmod_val (e m)
  have hn : (n.val:ZMod N)=e n := by rw [←val_e n];exact ZMod.natCast_zmod_val (e n)
  have he : (-(e m*e n):ZMod N)=((-((m.val:Int)*(n.val:Int)):Int):ZMod N) := by
    push_cast
    rw [hm,hn]
  rw [he,ZMod.stdAddChar_coe]
  unfold RHBatch01ChirpDFT.phase
  congr 1
  push_cast
  ring
lemma character_positive (m n : Fin N) :
    ZMod.stdAddChar (N:=N) (e m*e n:ZMod N)=RHBatch01Fourier.phase ((m.val:ℝ)*(n.val:ℝ)/(N:ℝ)) := by
  have hm : (m.val:ZMod N)=e m := by rw [←val_e m];exact ZMod.natCast_zmod_val (e m)
  have hn : (n.val:ZMod N)=e n := by rw [←val_e n];exact ZMod.natCast_zmod_val (e n)
  have he : (e m*e n:ZMod N)=(((m.val:Int)*(n.val:Int):Int):ZMod N) := by push_cast;rw [hm,hn]
  rw [he,ZMod.stdAddChar_coe]
  unfold RHBatch01Fourier.phase
  congr 1
  push_cast
  ring
lemma dft_eq (a : Fin N→ℂ) (n : Fin N) :
    RHBatch01ChirpDFT.dft a n=ZMod.dft (N:=N) (lift a) (e n) := by
  rw [ZMod.dft_apply]
  unfold RHBatch01ChirpDFT.dft
  apply Fintype.sum_equiv e
  intro m
  simp only [lift,Equiv.symm_apply_apply,character,smul_eq_mul]
  ring
lemma inverse_pair (a c : Fin N→ℂ) (B : ℝ) (hB : 0 < B)
    (h : ∀ n, a n=(B⁻¹:ℂ)*∑ m : Fin N,
      c m*RHBatch01Fourier.phase ((m.val:ℝ)*(n.val:ℝ)/(N:ℝ))) :
    ∀ m, c m=((B/(N:ℝ):ℝ):ℂ)*RHBatch01ChirpDFT.dft a m := by
  have hfun : lift a=((N:ℂ)/(B:ℂ)) • ((ZMod.dft (N:=N)).symm (lift c)) := by
    funext j
    obtain ⟨n,rfl⟩ := e.surjective j
    simp only [lift,Equiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul]
    rw [h n,ZMod.invDFT_apply]
    simp only [smul_eq_mul]
    have he : (∑ m : ZMod N, ZMod.stdAddChar (m*e n)*lift c m)=
        ∑ m : Fin N, c m*RHBatch01Fourier.phase ((m.val:ℝ)*(n.val:ℝ)/(N:ℝ)) := by
      symm
      apply Fintype.sum_equiv e
      intro m
      simp only [lift,Equiv.symm_apply_apply,character_positive]
      ring
    rw [he]
    have hb : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
    field_simp [hb,show (N:ℂ)≠0 from by exact_mod_cast NeZero.ne N]
    simp only [mul_comm]
  have hout := congrArg (ZMod.dft (N:=N)) hfun
  rw [map_smul,LinearEquiv.apply_symm_apply] at hout
  intro m
  have hm := congrFun hout (e m)
  simp only [Pi.smul_apply,smul_eq_mul,lift,Equiv.symm_apply_apply] at hm
  rw [dft_eq,hm]
  have hb : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  push_cast
  field_simp [hb,show (N:ℂ)≠0 from by exact_mod_cast NeZero.ne N]
end RHBatch01GenericDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000
open Complex
namespace RHBatch01CenteredDFT
open RHBatch01GenericDFT
variable {N : Nat} [NeZero N]
lemma phase_add (x y : ℝ) : RHBatch01Fourier.phase (x+y)=RHBatch01Fourier.phase x*RHBatch01Fourier.phase y := by
  unfold RHBatch01Fourier.phase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_inv (x : ℝ) : RHBatch01Fourier.phase (-x)*RHBatch01Fourier.phase x=1 := by
  rw [←phase_add]
  simp [RHBatch01Fourier.phase]
lemma inverse_pair (a c : Fin N→ℂ) (B H : ℝ) (hB : 0 < B)
    (h : ∀ n, a n=(B⁻¹:ℂ)*∑ m : Fin N,
      c m*RHBatch01Fourier.phase ((m.val:ℝ)*((n.val:ℝ)+H)/(N:ℝ))) :
    ∀ m, c m=RHBatch01Fourier.phase (-(m.val:ℝ)*H/(N:ℝ))*
      (((B/(N:ℝ):ℝ):ℂ)*RHBatch01ChirpDFT.dft a m) := by
  let c' : Fin N→ℂ := fun m => c m*RHBatch01Fourier.phase ((m.val:ℝ)*H/(N:ℝ))
  have he : ∀ n, a n=(B⁻¹:ℂ)*∑ m : Fin N,
      c' m*RHBatch01Fourier.phase ((m.val:ℝ)*(n.val:ℝ)/(N:ℝ)) := by
    intro n
    rw [h n]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [show (m.val:ℝ)*((n.val:ℝ)+H)/(N:ℝ)=
      (m.val:ℝ)*H/(N:ℝ)+(m.val:ℝ)*(n.val:ℝ)/(N:ℝ) by ring,phase_add]
    dsimp [c']
    ring
  have hh := RHBatch01GenericDFT.inverse_pair a c' B hB he
  intro m
  rw [←hh m]
  dsimp [c']
  have hp : -(m.val:ℝ)*H/(N:ℝ)= -((m.val:ℝ)*H/(N:ℝ)) := by ring
  rw [hp]
  calc
    _ = c m*1 := by rw [mul_one]
    _ = c m*(RHBatch01Fourier.phase (-((m.val:ℝ)*H/(N:ℝ)))*RHBatch01Fourier.phase ((m.val:ℝ)*H/(N:ℝ))) := by rw [phase_inv]
    _ = _ := by ring
end RHBatch01CenteredDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHBatch01CenteredDFT
variable {N : Nat} [NeZero N]
lemma inverse_pair_error_at (p a c : Fin N→ℂ) (d : ℂ) (m : Fin N) (B H εt εd εf : ℝ) (hB : 0 < B)
    (hp : ∀ n, p n=(B⁻¹:ℂ)*∑ m : Fin N,
      c m*RHBatch01Fourier.phase ((m.val:ℝ)*((n.val:ℝ)+H)/(N:ℝ)))
    (ht : ∀ n, ‖p n-a n‖≤εt) (hd : ‖RHBatch01ChirpDFT.dft a m-d‖≤εd)
    (F : ℂ) (hf : ‖F-c m‖≤εf) :
    ‖F-RHBatch01Fourier.phase (-(m.val:ℝ)*H/(N:ℝ))*(((B/(N:ℝ):ℝ):ℂ)*d)‖≤
      εf+B*εt+(B/(N:ℝ))*εd := by
  have hc := inverse_pair p c B H hB hp m
  have hN : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : ‖RHBatch01ChirpDFT.dft p m-d‖≤(N:ℝ)*εt+εd :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (RHBatch01ChirpDFT.dft_error p a εt ht m) (hd))
  have he : ‖c m-RHBatch01Fourier.phase (-(m.val:ℝ)*H/(N:ℝ))*(((B/(N:ℝ):ℝ):ℂ)*d)‖≤
      B*εt+(B/(N:ℝ))*εd := by
    rw [hc,←mul_sub,←mul_sub,norm_mul,RHBatch01Fourier.phase_norm,one_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hB hN)]
    calc
      _ ≤ (B/(N:ℝ))*((N:ℝ)*εt+εd) := mul_le_mul_of_nonneg_left hs (div_pos hB hN).le
      _ = _ := by field_simp
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hf he)).trans_eq (by ring)
end RHBatch01CenteredDFT
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology
namespace RHBatch01Contour
lemma horizontal_shift (f : ℂ→ℂ) (α : ℝ) (hf : Differentiable ℂ f)
    (h0 : Integrable (fun x : ℝ => f (x:ℂ)))
    (hα : Integrable (fun x : ℝ => f ((x:ℂ)+(α:ℂ)*I)))
    (hv : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I)) atTop (𝓝 0))
    (hvneg : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I)) atBot (𝓝 0)) :
    (∫ x : ℝ, f (x:ℂ))=∫ x : ℝ, f ((x:ℂ)+(α:ℂ)*I) := by
  have ht0 := intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have htα := intervalIntegral_tendsto_integral hα tendsto_neg_atTop_atBot tendsto_id
  have ht := (((ht0.sub htα).add (hv.const_mul I)).sub
    ((hvneg.comp tendsto_neg_atTop_atBot).const_mul I))
  have he (R : ℝ) :
      (∫ x : ℝ in -R..R, f (x:ℂ))-
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(α:ℂ)*I))+
        I*(∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I))-
        I*(∫ y : ℝ in 0..α, f (((-R:ℝ):ℂ)+(y:ℂ)*I))=0 := by
    have hr := integral_boundary_rect_eq_zero_of_differentiableOn f (-R:ℂ)
      ((R:ℂ)+(α:ℂ)*I) hf.differentiableOn
    simpa only [neg_re,neg_im,neg_zero,ofReal_zero,ofReal_re,ofReal_im,add_re,mul_re,I_re,mul_zero,
      mul_im,I_im,mul_one,sub_zero,add_zero,add_im,zero_add,ofReal_neg,
      zero_mul,smul_eq_mul] using hr
  have hz : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in -R..R, f (x:ℂ))-
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(α:ℂ)*I))+
        I*(∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I))-
        I*(∫ y : ℝ in 0..α, f (((-R:ℝ):ℂ)+(y:ℂ)*I))) atTop (𝓝 0) := by
    simpa only [he] using (tendsto_const_nhds (x:=(0:ℂ)) (f:=atTop))
  have heq := tendsto_nhds_unique ht hz
  simpa using sub_eq_zero.mp (by simpa using heq)
end RHBatch01Contour
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaFourier
noncomputable def logKernel (s : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-(Real.exp y:ℂ)+s*(y:ℂ))
lemma gamma_log_integral (s : ℂ) (hs : 0<s.re) :
    Complex.Gamma s=∫ y : ℝ, logKernel s y := by
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral]
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ: Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))
  have him : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by
    simpa using Real.range_exp
  rw [him] at hi
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma gaussian_factor (h : ℝ) (hh : 0<h) :
    ((Real.pi:ℂ)/(1/(2*(h:ℂ)^2)))^(1/2:ℂ)=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ) := by
  have he : (Real.pi:ℂ)/(1/(2*(h:ℂ)^2))=((2*Real.pi*h^2:ℝ):ℂ) := by push_cast;field_simp <;> ring
  rw [he]
  have hx : (0:ℝ)≤2*Real.pi*h^2 := by positivity
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hx,←Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh,Complex.ofReal_mul]
lemma exponential_gaussian_fourier (h : ℝ) (hh : 0<h) (a x : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)) x=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        Complex.exp ((h:ℂ)^2/2*((a:ℂ)-2*(Real.pi:ℂ)*I*x)^2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,←Complex.exp_add]
  have he (t : ℝ) : ((-2*Real.pi*t*x:ℝ):ℂ)*I+
      (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)=
      (-1/(2*(h:ℂ)^2))*(t:ℂ)^2+((a:ℂ)-2*(Real.pi:ℂ)*I*x)*t+0 := by push_cast;ring
  simp_rw [he]
  have hb : (-1/(2*(h:ℂ)^2)).re<0 := by
    have he : (-1/(2*(h:ℂ)^2))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  rw [integral_cexp_quadratic hb]
  have hf : -( -1/(2*(h:ℂ)^2))=1/(2*(h:ℂ)^2) := by ring
  rw [hf,gaussian_factor h hh]
  congr 1
  congr 1
  field_simp
  ring
lemma log_kernel_exp_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp (-Real.exp y):ℂ)*(Real.exp y:ℂ)^(s-1))=logKernel s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma log_kernel_integrable (s : ℂ) (hs : 0<s.re) : Integrable (logKernel s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))).mp
      (he.symm ▸ Complex.GammaIntegral_convergent hs)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),
    log_kernel_exp_rewrite] using hi
noncomputable def window (T h t : ℝ) : ℂ :=
  Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
noncomputable def gammaWindow (T h t : ℝ) : ℂ :=
  Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t
noncomputable def Q (T h x y : ℝ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
    Complex.exp ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*
      ((Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)
noncomputable def joint (T h x t y : ℝ) : ℂ :=
  logKernel (1/4+(((t+T)/2:ℝ):ℂ)*I) y*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma window_integrable (T h : ℝ) (hh : 0<h) : Integrable (window T h) := by
  have hb : (-(1/(2*(h:ℂ)^2))).re<0 := by
    have he : (-(1/(2*(h:ℂ)^2)))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;ring
    rw [he,ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : window T h t=Complex.exp (
    (-(1/(2*(h:ℂ)^2)))*(t:ℂ)^2+(Real.pi/4:ℝ)*t+(Real.pi*T/4:ℝ)) := by
    unfold window
    congr 1
    push_cast
    ring
  change Integrable (fun t : ℝ => window T h t)
  simp_rw [he]
  exact integrable_cexp_quadratic' hb _ _
lemma log_kernel_norm (s : ℂ) (y : ℝ) :
    ‖logKernel s y‖=Real.exp (-Real.exp y+s.re*y) := by
  rw [logKernel,Complex.norm_exp]
  congr 1
  simp only [add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma joint_norm (T h x t y : ℝ) :
    ‖joint T h x t y‖=‖window T h t‖*‖logKernel (1/4) y‖ := by
  unfold joint
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_kernel_norm,log_kernel_norm]
  have hr : (1/4+(((t+T)/2:ℝ):ℂ)*I:ℂ).re=(1/4:ℂ).re := by simp
  rw [hr]
  ring
lemma joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    (log_kernel_integrable (1/4) (by norm_num)).norm
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
      unfold joint logKernel window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (joint_norm T h x p.1 p.2).le
lemma inner_joint (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, joint T h x t y)=
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  let b : ℂ := -1/(2*(h:ℂ)^2)
  let c : ℂ := (Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ)
  let d : ℂ := (-Real.exp y+y/4+Real.pi*T/4:ℝ)+I*(T:ℂ)*y/2
  have hb : b.re<0 := by
    have he : b=((-1/(2*h^2):ℝ):ℂ) := by dsimp [b];push_cast;ring
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : joint T h x t y=Complex.exp (b*(t:ℂ)^2+c*t+d) := by
    unfold joint logKernel window
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    dsimp [b,c,d]
    push_cast
    ring
  simp_rw [he]
  rw [integral_cexp_quadratic hb]
  have hn : -b=1/(2*(h:ℂ)^2) := by dsimp [b];ring
  rw [hn,gaussian_factor h hh]
  have hr : d-c^2/(4*b)=((-Real.exp y+y/4:ℝ):ℂ)+
      ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*c^2+I*(T:ℂ)*y/2) := by
    dsimp [b,d]
    push_cast
    field_simp
    ring
  rw [hr,Complex.exp_add]
  dsimp [Q,c]
  ring
lemma gamma_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (gammaWindow T h) x=
      ∫ y : ℝ, Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, joint T h x t y)=
      Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t*
        Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [joint,integral_mul_const]
    rw [←gamma_log_integral _ (by norm_num)]
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, joint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      dsimp [gammaWindow]
      ring
    _ = ∫ y : ℝ, ∫ t : ℝ, joint T h x t y :=
      integral_integral_swap (joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact inner_joint T h x y hh
end RHBatch01GammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GammaFourier
lemma Q_norm (T h x y : ℝ) (hh : 0<h) :
    ‖Q T h x y‖=Real.sqrt (2*Real.pi)*h*
      Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2) := by
  rw [Q,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hh,
    Complex.norm_exp]
  congr 1
  simp only [add_re,mul_re,div_re,ofReal_re,ofReal_im,I_re,I_im,pow_two]
  norm_num
  ring
lemma real_quadratic_integrable (b c d : ℝ) (hb : b<0) :
    Integrable (fun y : ℝ => Real.exp (b*y^2+c*y+d)) := by
  have h := (integrable_cexp_quadratic' (b:= (b:ℂ)) (by simpa using hb) (c:ℂ) (d:ℂ)).norm
  convert! h using 1
  ext y
  rw [Complex.norm_exp]
  congr 1
  simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_add,Complex.ofReal_re]
noncomputable def Qmajorant (T h x y : ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi)*h/Real.pi)*
    Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4)
lemma Qmajorant_integrable (T h x : ℝ) (hh : 0<h) : Integrable (Qmajorant T h x) := by
  have he (y : ℝ) : Qmajorant T h x y=(Real.sqrt (2*Real.pi)*h/Real.pi)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x-3/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    unfold Qmajorant
    congr 1
    congr 1
    ring
  change Integrable (fun y : ℝ => Qmajorant T h x y)
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
lemma Qweighted_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Real.exp (y/4)*‖Q T h x y‖) := by
  have he (y : ℝ) : Real.exp (y/4)*‖Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [Q_norm T h x y hh]
    have hp : (y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*
        (Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
end RHBatch01GammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaFourier
noncomputable def dirichletWeight (T a : ℝ) : ℂ :=
  Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))
lemma Q_translation (T h x y a : ℝ) (ha : 0<a) :
    Q T h (x+Real.log a/(2*Real.pi)) (y+2*Real.log a)=
      Q T h x y*Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)) := by
  unfold Q
  have he : ((y+2*Real.log a)/2-2*Real.pi*(x+Real.log a/(2*Real.pi)):ℝ)=
      y/2-2*Real.pi*x := by field_simp;ring
  rw [he]
  conv_rhs => rw [mul_assoc,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma gamma_fourier_dirichlet_shift (T h x a : ℝ) (hh : 0<h) (ha : 0<a) :
    dirichletWeight T a*𝓕 (gammaWindow T h) (x+Real.log a/(2*Real.pi))=
      ∫ y : ℝ, Complex.exp ((-a^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  rw [gamma_window_fourier T h _ hh]
  rw [←integral_const_mul]
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ =>
    dirichletWeight T a*(Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*
      Q T h (x+Real.log a/(2*Real.pi)) y)) (2*Real.log a)
  rw [←ht]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Q_translation T h x y a ha]
  have hexp : Real.exp (y+2*Real.log a)=a^2*Real.exp y := by
    rw [Real.exp_add,show 2*Real.log a=Real.log a+Real.log a by ring,Real.exp_add,Real.exp_log ha]
    ring
  rw [hexp]
  unfold dirichletWeight
  have he : -(1/2+I*(T:ℂ))*(Real.log a:ℂ)+
      ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)+
      I*(T:ℂ)*(Real.log a:ℂ)=((-a^2*Real.exp y+y/4:ℝ):ℂ) := by push_cast;ring
  calc
    _ = (Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))*
      Complex.exp ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)*
      Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)))*Q T h x y := by ring
    _ = _ := by rw [←Complex.exp_add,←Complex.exp_add,he]
end RHBatch01GammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Real MeasureTheory Set HurwitzZeta Filter
open scoped Topology
namespace RHBatch01ThetaSeries
noncomputable def psi (u : ℝ) : ℝ := (evenKernel 0 u-1)/2
lemma hasSum_psi (u : ℝ) (hu : 0<u) :
    HasSum (fun n : Nat => Real.exp (-Real.pi*(n+1:ℝ)^2*u)) (psi u) := by
  have h := (hasSum_nat_cosKernel₀ 0 hu).div_const 2
  convert! h using 1
  · ext n
    simp
  · simp only [QuotientAddGroup.mk_zero]
    rw [←evenKernel_eq_cosKernel_of_zero]
    rfl
lemma psi_nonneg (u : ℝ) (hu : 0<u) : 0≤psi u := by
  rw [←(hasSum_psi u hu).tsum_eq]
  exact tsum_nonneg (fun n => (Real.exp_pos _).le)
lemma psi_le (u : ℝ) (hu : 0<u) : psi u≤1/(Real.pi*u) := by
  let q := Real.exp (-Real.pi*u)
  have hp : 0<Real.pi*u := mul_pos Real.pi_pos hu
  have hqp : 0<q := Real.exp_pos _
  have hq1 : q<1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hqn : ‖q‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hqp] using hq1
  have hg : HasSum (fun n : Nat => q^(n+1)) (q/(1-q)) := by
    convert! (hasSum_geometric_of_norm_lt_one hqn).mul_left q using 1
    · ext n
      rw [pow_succ]
      ring
  have hb (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*u)≤q^(n+1) := by
    have hn : 1≤(n+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) n; linarith
    have hpow : (n+1:ℝ)≤(n+1:ℝ)^2 := by nlinarith
    have he : q^(n+1)=Real.exp (-Real.pi*(n+1:ℝ)*u) := by
      dsimp [q]
      rw [←Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow hp.le]
  have hs : psi u≤q/(1-q) := by
    rw [←(hasSum_psi u hu).tsum_eq,←hg.tsum_eq]
    exact (hasSum_psi u hu).summable.tsum_le_tsum hb hg.summable
  have hexp : q*Real.exp (Real.pi*u)=1 := by
    dsimp [q]
    rw [←Real.exp_add]
    simp
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.pi*u)) hqp.le
  rw [hexp] at he
  apply hs.trans
  apply (div_le_div_iff₀ (by linarith : 0<1-q) hp).mpr
  nlinarith
lemma finite_psi_sum_le (u : ℝ) (hu : 0<u) (N : Nat) :
    (∑ n ∈ Finset.range N, Real.exp (-Real.pi*(n+1:ℝ)^2*u))≤1/(Real.pi*u) := by
  apply le_trans _ (psi_le u hu)
  rw [←(hasSum_psi u hu).tsum_eq]
  exact (hasSum_psi u hu).summable.sum_le_tsum (Finset.range N) (fun n _ => (Real.exp_pos _).le)
end RHBatch01ThetaSeries
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01ThetaGamma
open RHBatch01GammaFourier RHBatch01ThetaSeries
noncomputable def seriesKernel (n : Nat) (T h x y : ℝ) : ℂ :=
  Complex.exp ((-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y
lemma series_kernel_norm (n : Nat) (T h x y : ℝ) :
    ‖seriesKernel n T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖ := by
  rw [seriesKernel,norm_mul,Complex.norm_exp,Complex.ofReal_re]
lemma series_kernel_integrable (n : Nat) (T h x : ℝ) (hh : 0<h) :
    Integrable (seriesKernel n T h x) := by
  have hc : Continuous (seriesKernel n T h x) := by unfold seriesKernel Q;fun_prop
  apply (Qweighted_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [series_kernel_norm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp : 0≤Real.pi*(n+1:ℝ)^2*Real.exp y := by positivity
  linarith
lemma Qmajorant_eq (T h x y : ℝ) (hh : 0<h) :
    Qmajorant T h x y=
      (1/(Real.pi*Real.exp y))*(Real.exp (y/4)*‖Q T h x y‖) := by
  rw [Q_norm T h x y hh]
  have he : 1/(Real.pi*Real.exp y)=(1/Real.pi)*Real.exp (-y) := by
    rw [Real.exp_neg]
    ring
  rw [he]
  have hp : (-y)+(y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
      Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4 := by ring
  unfold Qmajorant
  calc
    _ = (1/Real.pi)*(Real.sqrt (2*Real.pi)*h)*
      (Real.exp (-y)*Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by
      rw [←Real.exp_add,←Real.exp_add,hp]
      ring
    _ = _ := by ring
lemma finite_kernel_norm_le (T h x y : ℝ) (hh : 0<h) (N : Nat) :
    (∑ n ∈ Finset.range N, ‖seriesKernel n T h x y‖)≤Qmajorant T h x y := by
  simp_rw [series_kernel_norm]
  have he (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by
    rw [Real.exp_add]
    ring
  simp_rw [he]
  rw [←Finset.sum_mul,Qmajorant_eq T h x y hh]
  exact mul_le_mul_of_nonneg_right (finite_psi_sum_le (Real.exp y) (Real.exp_pos _) N) (by positivity)
lemma kernel_integral_norm_summable (T h x : ℝ) (hh : 0<h) :
    Summable (fun n : Nat => ∫ y : ℝ, ‖seriesKernel n T h x y‖) := by
  apply summable_of_sum_range_le (fun n => integral_nonneg (fun y => norm_nonneg _))
  intro N
  rw [←integral_finset_sum (Finset.range N) (fun n _ => (series_kernel_integrable n T h x hh).norm)]
  exact integral_mono (integrable_finsetSum _ (fun n _ => (series_kernel_integrable n T h x hh).norm))
    (Qmajorant_integrable T h x hh) (fun y => finite_kernel_norm_le T h x y hh N)
lemma hasSum_kernel_point (T h x y : ℝ) :
    HasSum (fun n : Nat => seriesKernel n T h x y)
      ((psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y) := by
  have hbase : HasSum (fun n : Nat => (Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y):ℂ))
      (psi (Real.exp y):ℂ) := hasSum_ofReal.mpr (hasSum_psi (Real.exp y) (Real.exp_pos _))
  have hsum := (hbase.mul_right (Complex.exp ((y/4:ℝ):ℂ))).mul_right (Q T h x y)
  convert! hsum using 1
  ext n
  unfold seriesKernel
  rw [Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma sum_kernel_integral (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, ∫ y : ℝ, seriesKernel n T h x y)=
      ∫ y : ℝ, (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y := by
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun n => series_kernel_integrable n T h x hh) (kernel_integral_norm_summable T h x hh)
  rw [hsum.tsum_eq]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (hasSum_kernel_point T h x y).tsum_eq
end RHBatch01ThetaGamma
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GammaFourier
lemma weighted_Q_integrable (c T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by
  have he (y : ℝ) : ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,Q_norm T h x y hh]
    have hp : c*y+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*(Real.exp (c*y)*
        Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  have hi : Integrable (fun y : ℝ => ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖) := by
    simp_rw [he]
    exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
  have hc : Continuous (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by unfold Q;fun_prop
  exact (integrable_norm_iff hc.aestronglyMeasurable).mp hi
end RHBatch01GammaFourier
namespace RHBatch01ThetaGamma
open RHBatch01GammaFourier RHBatch01ThetaSeries
noncomputable def psiKernel (T h x y : ℝ) : ℂ :=
  (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
lemma psi_kernel_integrable (T h x : ℝ) (hh : 0<h) : Integrable (psiKernel T h x) := by
  have ht : Continuous (fun y : ℝ => HurwitzZeta.evenKernel 0 (Real.exp y)) :=
    (HurwitzZeta.continuousOn_evenKernel 0).comp_continuous Real.continuous_exp (fun y => Real.exp_pos y)
  have hc : Continuous (psiKernel T h x) := by
    have hp : Continuous (fun y : ℝ => psi (Real.exp y)) := by
      unfold psi
      exact (ht.sub continuous_const).div_const _
    unfold psiKernel Q
    fun_prop
  apply (Qmajorant_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [psiKernel,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (psi_nonneg (Real.exp y) (Real.exp_pos _)),Complex.norm_exp,Complex.ofReal_re]
  rw [Qmajorant_eq T h x y hh]
  have he : psi (Real.exp y)*Real.exp (y/4)*‖Q T h x y‖=
      psi (Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (psi_le (Real.exp y) (Real.exp_pos _)) (by positivity)
end RHBatch01ThetaGamma
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace RHBatch01GammaRotation
open RHBatch01GammaFourier
noncomputable def kernel (T h x : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*Complex.exp (-Complex.exp z+z/4+
    ((Real.pi*T/4:ℝ):ℂ)+(h:ℂ)^2/2*
      (((Real.pi/4:ℝ):ℂ)+I*(z/2-((2*Real.pi*x:ℝ):ℂ)))^2+I*(T:ℂ)*z/2)
lemma kernel_real (T h x y : ℝ) :
    kernel T h x (y:ℂ)=Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  unfold kernel Q
  have he : -(Complex.exp (y:ℂ))+(y:ℂ)/4+((Real.pi*T/4:ℝ):ℂ)+
      (h:ℂ)^2/2*(((Real.pi/4:ℝ):ℂ)+I*((y:ℂ)/2-((2*Real.pi*x:ℝ):ℂ)))^2+I*(T:ℂ)*y/2=
      ((-Real.exp y+y/4:ℝ):ℂ)+(((Real.pi*T/4:ℝ):ℂ)+(h:ℂ)^2/2*
        (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2) := by
    rw [←Complex.ofReal_exp]
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring
lemma kernel_norm (T h x y α : ℝ) (hh : 0<h) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖=Real.sqrt (2*Real.pi)*h*
      Real.exp (-Real.exp y*Real.cos α+y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2) := by
  rw [kernel,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hh,Complex.norm_exp]
  congr 2
  norm_num [add_re,neg_re,div_re,mul_re,pow_two,ofReal_re,ofReal_im,I_re,I_im,
    mul_im,add_im,sub_re,sub_im,exp_re,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,mul_one,one_mul,div_im,neg_im]
  ring
noncomputable def majorant (T h x y : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*h*Real.exp (y/4+Real.pi*T/4+h^2*Real.pi^2/32-
    h^2/2*(y/2-2*Real.pi*x)^2)
lemma kernel_norm_le (T h x y α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ ≤ majorant T h x y := by
  rw [kernel_norm T h x y α hh]
  unfold majorant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hc : 0≤Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hα'⟩
  have hs : (Real.pi/4-α/2)^2≤Real.pi^2/16 := by
    nlinarith [Real.pi_pos]
  have hn : 0≤Real.exp y*Real.cos α := mul_nonneg (Real.exp_pos _).le hc
  have ht : 0≤T*α := mul_nonneg hT hα
  nlinarith [sq_nonneg h,mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hs)]
lemma majorant_integrable (T h x : ℝ) (hh : 0<h) : Integrable (majorant T h x) := by
  convert (weighted_Q_integrable (1/4) T h x hh).norm using 1
  ext y
  rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,Q_norm T h x y hh]
  unfold majorant
  symm
  calc
    _ = Real.sqrt (2*Real.pi)*h*(Real.exp (y/4)*
      Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring
lemma negative_quadratic_limit (b c d : ℝ) (hb : b<0) :
    Tendsto (fun y : ℝ => Real.exp (b*y^2+c*y+d)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have ht : Tendsto (fun y : ℝ => ((-b)*y-c)*y-d) atTop atTop := by
    apply tendsto_atTop_add_const_right
    apply Tendsto.atTop_mul_atTop₀ _ tendsto_id
    apply tendsto_atTop_add_const_right
    exact (tendsto_const_mul_atTop_of_pos (by linarith : 0 < -b)).mpr tendsto_id
  convert tendsto_neg_atTop_atBot.comp ht using 1
  ext y
  dsimp
  ring
end RHBatch01GammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace RHBatch01GammaRotation
open RHBatch01GammaFourier RHBatch01Contour
lemma majorant_limits (T h x : ℝ) (hh : 0<h) :
    Tendsto (majorant T h x) atTop (𝓝 0) ∧ Tendsto (majorant T h x) atBot (𝓝 0) := by
  let b : ℝ := -h^2/8
  let c : ℝ := h^2*Real.pi*x+1/4
  let d : ℝ := Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2
  have hb : b<0 := by dsimp [b];nlinarith [sq_pos_of_pos hh]
  have he (y : ℝ) : majorant T h x y=Real.sqrt (2*Real.pi)*h*Real.exp (b*y^2+c*y+d) := by
    unfold majorant
    congr 2
    dsimp [b,c,d]
    ring
  constructor
  · simpa only [←he,mul_zero] using (negative_quadratic_limit b c d hb).const_mul (Real.sqrt (2*Real.pi)*h)
  · have ht := (negative_quadratic_limit b (-c) d hb).comp tendsto_neg_atBot_atTop
    have he' : (fun y : ℝ => Real.exp (b*(-y)^2+(-c)*(-y)+d))=
        (fun y : ℝ => Real.exp (b*y^2+c*y+d)) := by ext y;congr 1;ring
    simp only [Function.comp_def] at ht
    rw [he'] at ht
    simpa only [←he,mul_zero] using ht.const_mul (Real.sqrt (2*Real.pi)*h)
lemma kernel_line_integrable (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    Integrable (fun y : ℝ => kernel T h x ((y:ℂ)+(α:ℂ)*I)) := by
  apply (majorant_integrable T h x hh).mono'
  · have hc : Continuous (fun y : ℝ => kernel T h x ((y:ℂ)+(α:ℂ)*I)) := by unfold kernel;fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with y
    exact kernel_norm_le T h x y α hT hh hα hα'
lemma kernel_vertical_bound (T h x α R : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    ‖∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)‖ ≤ majorant T h x R*α := by
  simpa only [sub_zero,abs_of_nonneg hα] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=α) (fun y hy =>
      kernel_norm_le T h x R y hT hh
        (by
          have hy' : y∈Ioc 0 α := by simpa only [uIoc_of_le hα] using hy
          exact hy'.1.le)
        (by
          have hy' : y∈Ioc 0 α := by simpa only [uIoc_of_le hα] using hy
          exact hy'.2.trans hα')))
lemma kernel_vertical_limits (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)) atBot (𝓝 0) := by
  have hb (R : ℝ) := kernel_vertical_bound T h x α R hT hh hα hα'
  have hl := majorant_limits T h x hh
  constructor
  all_goals
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    · first | simpa using hl.1.mul_const α | simpa using hl.2.mul_const α
    · exact Eventually.of_forall (fun R => norm_nonneg _)
    · exact Eventually.of_forall hb
lemma gamma_contour_rotation (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    𝓕 (gammaWindow T h) x=∫ y : ℝ, kernel T h x ((y:ℂ)+(α:ℂ)*I) := by
  rw [gamma_window_fourier T h x hh]
  have he : (fun y : ℝ => Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y)=
      (fun y : ℝ => kernel T h x (y:ℂ)) := by ext y;rw [kernel_real]
  rw [he]
  have hd : Differentiable ℂ (kernel T h x) := by unfold kernel;fun_prop
  have hz := kernel_line_integrable T h x 0 hT hh (by norm_num) (by positivity)
  have h0 : Integrable (fun y : ℝ => kernel T h x (y:ℂ)) := by simpa using hz
  exact horizontal_shift _ α hd h0 (kernel_line_integrable T h x α hT hh hα hα')
    (kernel_vertical_limits T h x α hT hh hα hα').1
    (kernel_vertical_limits T h x α hT hh hα hα').2
end RHBatch01GammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaRotation
open RHBatch01GammaFourier
lemma integral_real_quadratic (b c d : ℝ) (hb : b<0) :
    (∫ y : ℝ, Real.exp (b*y^2+c*y+d))=
      Real.sqrt (Real.pi/(-b))*Real.exp (d-c^2/(4*b)) := by
  have he (y : ℝ) : b*y^2+c*y+d=b*(y+c/(2*b))^2+(d-c^2/(4*b)) := by
    field_simp [hb.ne]
    ring
  simp_rw [he,Real.exp_add]
  rw [integral_mul_const,integral_add_right_eq_self (μ:=(volume:Measure ℝ))
    (fun y : ℝ => Real.exp (b*y^2)) (c/(2*b))]
  have hg : (fun y : ℝ => Real.exp (b*y^2))=(fun y : ℝ => Real.exp (-(-b)*y^2)) := by
    ext y
    simp
  rw [hg,integral_gaussian]
lemma gaussian_prefactor (h : ℝ) (hh : 0<h) :
    Real.sqrt (2*Real.pi)*h*Real.sqrt (Real.pi/(h^2/8))=4*Real.pi := by
  have he : Real.pi/(h^2/8)=8*Real.pi/h^2 := by ring
  rw [he,Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh]
  have hs : Real.sqrt (8*Real.pi)=2*Real.sqrt (2*Real.pi) := by
    rw [show 8*Real.pi=4*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt 4=2 by norm_num]
  rw [hs]
  calc
    _ = 2*(Real.sqrt (2*Real.pi))^2 := by field_simp [hh.ne'] <;> ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)];ring
lemma kernel_half_pi_mass (T h x : ℝ) (hh : 0<h) :
    (∫ y : ℝ, ‖kernel T h x ((y:ℂ)+((Real.pi/2:ℝ):ℂ)*I)‖)=
      4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)) := by
  simp_rw [kernel_norm T h x _ _ hh,Real.cos_pi_div_two]
  have he (y : ℝ) : -Real.exp y*0+y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-(Real.pi/2)/2)^2-(y/2-2*Real.pi*x)^2)-T*(Real.pi/2)/2=
      (-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y-2*h^2*Real.pi^2*x^2 := by ring
  simp_rw [he]
  rw [integral_const_mul]
  simp only [sub_eq_add_neg]
  rw [integral_real_quadratic _ _ _ (by nlinarith [sq_pos_of_pos hh])]
  have hb : -(-h^2/8)=h^2/8 := by ring
  rw [hb,←mul_assoc,gaussian_prefactor h hh]
  congr 2
  field_simp [hh.ne']
  ring
lemma gamma_fourier_negative_bound (T h x : ℝ) (hT : 0≤T) (hh : 0<h) :
    ‖𝓕 (gammaWindow T h) x‖ ≤ 4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)) := by
  rw [gamma_contour_rotation T h x (Real.pi/2) hT hh (by positivity) le_rfl]
  exact (norm_integral_le_integral_norm _).trans_eq (kernel_half_pi_mass T h x hh)
end RHBatch01GammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set
namespace RHBatch01MomentEnvelope
lemma exp_neg_le_factorial_div_pow (v : ℝ) (hv : 0<v) (M : Nat) :
    Real.exp (-v)≤(M.factorial:ℝ)/v^M := by
  have hp := Real.pow_div_factorial_le_exp v hv.le M
  have hf : (0:ℝ)<M.factorial := by exact_mod_cast Nat.factorial_pos M
  rw [div_le_iff₀ hf] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-v)).le
  have he : Real.exp v*(M.factorial:ℝ)*Real.exp (-v)=(M.factorial:ℝ) := by
    calc
      _ = M.factorial*(Real.exp v*Real.exp (-v)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  rw [he] at hm
  exact (le_div_iff₀ (pow_pos hv M)).mpr (by simpa [mul_comm] using hm)
lemma exp_exp_moment_envelope (u y : ℝ) (hu : 0<u) (M : Nat) :
    Real.exp (-u*Real.exp y)≤((M.factorial:ℝ)/u^M)*Real.exp (-(M:ℝ)*y) := by
  have hp := exp_neg_le_factorial_div_pow (u*Real.exp y) (mul_pos hu (Real.exp_pos _)) M
  have he : (Real.exp y)^M=Real.exp ((M:ℝ)*y) := (Real.exp_nat_mul y M).symm
  have hne : Real.exp ((M:ℝ)*y)≠0 := (Real.exp_pos _).ne'
  rw [mul_pow,he] at hp
  have hr : (M.factorial:ℝ)/(u^M*Real.exp ((M:ℝ)*y))=
      ((M.factorial:ℝ)/u^M)*Real.exp (-(M:ℝ)*y) := by
    rw [show -(M:ℝ)*y= -((M:ℝ)*y) by ring,Real.exp_neg]
    ring
  simpa only [neg_mul,hr] using hp
lemma sin_small_lower (δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1/100) :
    (999/1000:ℝ)*δ≤Real.sin δ := by
  have hs := Real.sin_ge_sub_cube hδ
  have hsq : δ^2≤1/10000 := by nlinarith
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hsq)]
end RHBatch01MomentEnvelope
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaRotation
open RHBatch01GammaFourier RHBatch01MomentEnvelope
noncomputable def momentMajorant (T h x α : ℝ) (M : Nat) (y : ℝ) : ℝ :=
  ((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h)*
    Real.exp ((1/4-(M:ℝ))*y+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)
lemma kernel_moment_le (T h x y α : ℝ) (M : Nat) (hh : 0<h) (hcos : 0<Real.cos α) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ ≤ momentMajorant T h x α M y := by
  rw [kernel_norm T h x y α hh]
  unfold momentMajorant
  have he : -Real.exp y*Real.cos α+y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2=
      -(Real.cos α)*Real.exp y+(y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2) := by ring
  rw [he,Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (exp_exp_moment_envelope (Real.cos α) y hcos M)
      (Real.exp_pos (y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)).le)
    (show 0≤Real.sqrt (2*Real.pi)*h by positivity)
  have he' : -(M:ℝ)*y+(y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)=
      (1/4-(M:ℝ))*y+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2 := by ring
  calc
    _ ≤ _ := hm
    _ = _ := by rw [mul_assoc,mul_assoc,←Real.exp_add,he'];ring
lemma moment_majorant_quadratic (T h x α y : ℝ) (M : Nat) :
    momentMajorant T h x α M y=
      (((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h))*
        Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4-(M:ℝ))*y+
          (Real.pi*T/4+h^2/2*(Real.pi/4-α/2)^2-2*h^2*Real.pi^2*x^2-T*α/2)) := by
  unfold momentMajorant
  congr 1
  congr 1
  ring
lemma moment_majorant_integrable (T h x α : ℝ) (M : Nat) (hh : 0<h) :
    Integrable (momentMajorant T h x α M) := by
  have he : momentMajorant T h x α M=(fun y : ℝ =>
      (((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h))*
        Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4-(M:ℝ))*y+
          (Real.pi*T/4+h^2/2*(Real.pi/4-α/2)^2-2*h^2*Real.pi^2*x^2-T*α/2))) := by
    ext y
    exact moment_majorant_quadratic T h x α y M
  rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
lemma moment_majorant_integral (T h x α : ℝ) (M : Nat) (hh : 0<h) :
    (∫ y : ℝ, momentMajorant T h x α M y)=
      (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
        Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
          2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*x*(1/4-(M:ℝ))) := by
  simp_rw [moment_majorant_quadratic]
  rw [integral_const_mul,integral_real_quadratic _ _ _ (by nlinarith [sq_pos_of_pos hh])]
  rw [show -(-h^2/8)=h^2/8 by ring]
  have hp : ((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h)*
      Real.sqrt (Real.pi/(h^2/8))=4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M := by
    rw [mul_assoc,gaussian_prefactor h hh]
    ring
  rw [←mul_assoc,hp]
  congr 2
  field_simp [hh.ne']
  ring
lemma gamma_fourier_moment_bound (T h x α : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) :
    ‖𝓕 (gammaWindow T h) x‖ ≤
      (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
        Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
          2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*x*(1/4-(M:ℝ))) := by
  rw [gamma_contour_rotation T h x α hT hh hα hα'.le]
  have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
  calc
    _ ≤ ∫ y : ℝ, ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, momentMajorant T h x α M y :=
      integral_mono (kernel_line_integrable T h x α hT hh hα hα'.le).norm
        (moment_majorant_integrable T h x α M hh) (fun y => kernel_moment_le T h x y α M hh hc)
    _ = _ := moment_majorant_integral T h x α M hh
end RHBatch01GammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set HurwitzZeta Filter Asymptotics
open scoped FourierTransform Topology
namespace RHBatch01ThetaFourier
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0
lemma modif_convergent (s : ℂ) : MellinConvergent P.f_modif s := by
  exact mellinConvergent_of_isBigO_rpow P.hf_modif_int
    (P.isStrongFEPair_toStrongFEPair.hf_top (-(s.re+1))) (by linarith)
    (P.isStrongFEPair_toStrongFEPair.hf_zero (-(s.re-1))) (by linarith)
lemma modif_one_lt (t : ℝ) (ht : 1<t) :
    P.f_modif t=(evenKernel 0 t:ℂ)-1 := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,not_lt.2 ht.le,Set.indicator_of_notMem]
lemma modif_lt_one (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    P.f_modif t=(evenKernel 0 t:ℂ)-(t^(-(1:ℝ)/2):ℝ) := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,ht1,not_lt.2 ht1.le]
  norm_num
noncomputable def logMellin (s : ℂ) (y : ℝ) : ℂ :=
  P.f_modif (Real.exp y)*Complex.exp (s*(y:ℂ))
lemma modif_log_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp y:ℂ)^(s-1)*P.f_modif (Real.exp y))=logMellin s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp]
  unfold logMellin
  have he : Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1))=Complex.exp (s*(y:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1)))*P.f_modif (Real.exp y) := by ring
    _ = _ := by rw [he];ring
lemma modif_log_integrable (s : ℂ) : Integrable (logMellin s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s-1)*P.f_modif u)).mp (he.symm ▸ modif_convergent s)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite] using hi
lemma completed_log_mellin (s : ℂ) :
    completedRiemannZeta₀ s=(∫ y : ℝ, logMellin (s/2) y)/2 := by
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s/2-1)*P.f_modif u)
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
  rw [he] at hi
  have hd : completedRiemannZeta₀ s=mellin P.f_modif (s/2)/2 := rfl
  rw [hd,mellin]
  simp only [smul_eq_mul]
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite]
open RHBatch01GammaFourier
noncomputable def thetaJoint (T h x t y : ℝ) : ℂ :=
  (logMellin ((1/2+((t+T:ℝ):ℂ)*I)/2) y/2)*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma log_mellin_norm (s : ℂ) (y : ℝ) :
    ‖logMellin s y‖=‖P.f_modif (Real.exp y)‖*Real.exp (s.re*y) := by
  rw [logMellin,norm_mul,Complex.norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma theta_joint_norm (T h x t y : ℝ) :
    ‖thetaJoint T h x t y‖=‖window T h t‖*(‖logMellin (1/4) y‖/2) := by
  unfold thetaJoint
  rw [norm_mul,norm_mul,norm_div,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_mellin_norm,log_mellin_norm]
  norm_num
  ring
lemma theta_joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => thetaJoint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    ((modif_log_integrable (1/4)).norm.div_const 2)
  apply hm.mono'
  · have hf := P.hf_modif_int.aestronglyMeasurable
    have hm : AEStronglyMeasurable (fun y : ℝ => P.f_modif (Real.exp y)) volume := by
      have hi := modif_log_integrable (0:ℂ)
      convert! hi.aestronglyMeasurable using 1
      ext y
      simp [logMellin]
    have he : Continuous (fun p : ℝ×ℝ =>
      Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I)) := by unfold window;fun_prop
    have hmeas : AEStronglyMeasurable (fun p : ℝ×ℝ =>
      P.f_modif (Real.exp p.2)*(Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I))) (volume.prod volume) :=
      hm.comp_snd.mul he.aestronglyMeasurable
    convert! hmeas using 1
    ext p
    dsimp [thetaJoint,logMellin]
    ring
  · filter_upwards [] with p
    exact (theta_joint_norm T h x p.1 p.2).le
lemma theta_joint_factor (T h x t y : ℝ) :
    thetaJoint T h x t y=
      (P.f_modif (Real.exp y)*Complex.exp (Real.exp y:ℂ)/2)*joint T h x t y := by
  unfold thetaJoint logMellin joint logKernel
  have he : ((1/2+((t+T:ℝ):ℂ)*I)/2)*(y:ℂ)=
      (Real.exp y:ℂ)+(-(Real.exp y:ℂ)+(1/4+(((t+T)/2:ℝ):ℂ)*I)*(y:ℂ)) := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring
lemma theta_joint_inner (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, thetaJoint T h x t y)=
      (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  simp_rw [theta_joint_factor]
  rw [integral_const_mul,inner_joint T h x y hh]
  have he : Complex.exp (Real.exp y:ℂ)*Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)=
      Complex.exp ((y/4:ℝ):ℂ) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (P.f_modif (Real.exp y)*(Complex.exp (Real.exp y:ℂ)*
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ))/2)*Q T h x y := by ring
    _ = _ := by rw [he]
noncomputable def entireWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta₀ (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma entire_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=
      ∫ y : ℝ, (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, thetaJoint T h x t y)=
      entireWindow T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [thetaJoint,integral_mul_const,integral_div]
    rw [←completed_log_mellin]
    rfl
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, thetaJoint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = ∫ y : ℝ, ∫ t : ℝ, thetaJoint T h x t y :=
      integral_integral_swap (theta_joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact theta_joint_inner T h x y hh
end RHBatch01ThetaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01PoleFourier
open RHBatch01GammaFourier
noncomputable def sline (ε T t : ℝ) : ℂ := 1/2+(ε:ℂ)*I*(t+T:ℝ)
lemma sline_re (ε T t : ℝ) : (sline ε T t).re=1/2 := by simp [sline]
noncomputable def poleJoint (ε T h x t y : ℝ) : ℂ :=
  Complex.exp (-(sline ε T t/2)*(y:ℂ))*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma laplace_half (s : ℂ) (hs : 0<s.re) :
    (∫ y : ℝ in Set.Ioi 0, Complex.exp (-(s/2)*(y:ℂ)))=2/s := by
  have h := integral_exp_mul_complex_Ioi (a:=-(s/2)) (by simp;linarith) 0
  simpa using h
lemma pole_joint_norm (ε T h x t y : ℝ) :
    ‖poleJoint ε T h x t y‖=‖window T h t‖*Real.exp (-y/4) := by
  rw [poleJoint,norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
  have hr : (-(sline ε T t/2)*(y:ℂ)).re= -y/4 := by simp [sline];ring
  rw [hr]
  ring
lemma pole_joint_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have hy : IntegrableOn (fun y : ℝ => Real.exp (-y/4)) (Set.Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (a:=(-1/4:ℝ)) (by norm_num) 0 using 1
    ext y
    congr 1
    ring
  have hm := (window_integrable T h hh).norm.mul_prod hy
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2) := by
      unfold poleJoint sline window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (pole_joint_norm ε T h x p.1 p.2).le
lemma pole_joint_factor (ε T h x t y : ℝ) :
    poleJoint ε T h x t y=
      Complex.exp ((Real.exp (-ε*y)-(-ε*y)/4-y/4:ℝ):ℂ)*joint T h x t (-ε*y) := by
  unfold poleJoint sline joint logKernel
  conv_rhs => rw [←mul_assoc,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
lemma pole_joint_inner (ε T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, poleJoint ε T h x t y)=
      Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  simp_rw [pole_joint_factor]
  rw [integral_const_mul,inner_joint T h x (-ε*y) hh]
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
noncomputable def poleWindow (ε T h t : ℝ) : ℂ := window T h t/sline ε T t
lemma pole_window_fourier (ε T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow ε T h) x=
      (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  have hi (t : ℝ) : (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y)=
      poleWindow ε T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [poleJoint,integral_mul_const]
    rw [laplace_half _ (by rw [sline_re];norm_num)]
    unfold poleWindow
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (1/2:ℂ)*∫ t : ℝ, ∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, ∫ t : ℝ, poleJoint ε T h x t y := by
      rw [integral_integral_swap (pole_joint_integrable ε T h x hh)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      exact pole_joint_inner ε T h x y hh
end RHBatch01PoleFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GammaFourier
lemma croot_of_pos (a : ℝ) (ha : 0<a) : (a:ℂ)^(1/2:ℂ)=(Real.sqrt a:ℂ) := by
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow ha.le,←Real.sqrt_eq_rpow]
lemma mass_prefactor (h : ℝ) (hh : 0<h) :
    (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2=2*(Real.pi:ℂ) := by
  have he : (Real.pi:ℂ)/(h^2/8)=((8*Real.pi/h^2:ℝ):ℂ) := by push_cast;ring
  rw [he,croot_of_pos _ (by positivity)]
  have hs : Real.sqrt (8*Real.pi/h^2)=2*Real.sqrt (2*Real.pi)/h := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh]
    rw [show (8*Real.pi:ℝ)=4*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs]
  have hn : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
  have hs2 : (Real.sqrt (2*Real.pi):ℂ)^2=2*(Real.pi:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  push_cast
  calc
    _ = (Real.sqrt (2*Real.pi):ℂ)^2 := by field_simp [hn] <;> ring
    _ = _ := hs2
lemma gaussian_pole_mass (T h x : ℝ) (hh : 0<h) :
    (1/2:ℂ)*(∫ y : ℝ, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y)=
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  let b : ℂ := -(h:ℂ)^2/8
  let c : ℂ := ((h^2*Real.pi*x-1/4:ℝ):ℂ)+I*((h^2*Real.pi/8+T/2:ℝ):ℂ)
  let d : ℂ := ((Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2:ℝ):ℂ)-I*((h^2*Real.pi^2*x/2:ℝ):ℂ)
  have hb : b.re<0 := by
    have he : b=((-h^2/8:ℝ):ℂ) := by dsimp [b];push_cast;rfl
    rw [he,ofReal_re]
    nlinarith [sq_pos_of_pos hh]
  have he (y : ℝ) : Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*Complex.exp (b*(y:ℂ)^2+c*y+d) := by
    unfold Q
    have hp : ((-y/4:ℝ):ℂ)+((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
        (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2=
        b*(y:ℂ)^2+c*y+d := by dsimp [b,c,d];push_cast;ring_nf <;> simp only [Complex.I_sq] <;> ring
    calc
      _ = (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        (Complex.exp ((-y/4:ℝ):ℂ)*Complex.exp (
          ((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
          (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)) := by ring
      _ = _ := by rw [←Complex.exp_add];congr 2;simpa only [add_assoc] using hp
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_quadratic hb]
  have hn : -b=(h:ℂ)^2/8 := by dsimp [b];ring
  rw [hn]
  have he : d-c^2/(4*b)=
      ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
      I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ) := by
    dsimp [b,c,d]
    push_cast
    have hne : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
    field_simp [hne]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  rw [he]
  have hp := mass_prefactor h hh
  calc
    _ = ((Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2)*
      Complex.exp (((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by ring
    _ = _ := by rw [hp]
end RHBatch01GammaFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01PlattFourier
open RHBatch01GammaFourier RHBatch01ThetaFourier RHBatch01ThetaGamma RHBatch01ThetaSeries
open RHBatch01PoleFourier
noncomputable def dirichletTerm (T h x : ℝ) (n : Nat) : ℂ :=
  dirichletWeight T ((n+1:ℝ)*Real.sqrt Real.pi)*
    𝓕 (gammaWindow T h) (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))
lemma dirichlet_term_eq (T h x : ℝ) (hh : 0<h) (n : Nat) :
    dirichletTerm T h x n=∫ y : ℝ, seriesKernel n T h x y := by
  unfold dirichletTerm
  rw [gamma_fourier_dirichlet_shift T h x _ hh (by positivity)]
  have he : ((n+1:ℝ)*Real.sqrt Real.pi)^2=Real.pi*(n+1:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt Real.pi_pos.le]
    ring
  simp only [he,seriesKernel,neg_mul]
lemma dirichlet_series_fourier (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, dirichletTerm T h x n)=∫ y : ℝ, psiKernel T h x y := by
  simp_rw [dirichlet_term_eq T h x hh]
  exact sum_kernel_integral T h x hh
noncomputable def positiveKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
noncomputable def negativeKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y
lemma positive_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (positiveKernel T h x) := by
  convert weighted_Q_integrable (1/4) T h x hh using 1
  ext y
  simp only [positiveKernel,one_div_mul_eq_div]
lemma negative_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (negativeKernel T h x) := by
  convert weighted_Q_integrable (-1/4) T h x hh using 1
  ext y
  unfold negativeKernel
  congr 2
  congr 1
  ring
lemma theta_kernel_eq (T h x : ℝ) :
    (fun y : ℝ => (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y)
      =ᵐ[volume] (fun y : ℝ => psiKernel T h x y+
        (Iio (0:ℝ)).indicator (fun y => (positiveKernel T h x y-negativeKernel T h x y)/2) y) := by
  have hae : ∀ᵐ y : ℝ ∂volume, y≠0 := by
    rw [ae_iff]
    simp
  filter_upwards [hae] with y hy
  rcases lt_or_gt_of_ne hy with hn|hp
  · rw [Set.indicator_of_mem (show y∈Iio (0:ℝ) from hn),modif_lt_one _ (Real.exp_pos _) (by simpa using hn)]
    have he : Real.exp y^(-(1:ℝ)/2)=Real.exp (-y/2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring
    rw [he]
    unfold psiKernel positiveKernel negativeKernel psi
    push_cast
    have hm : (Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ)=
        Complex.exp ((-y/4:ℝ):ℂ) := by
      rw [Complex.ofReal_exp,←Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (((HurwitzZeta.evenKernel 0 (Real.exp y):ℂ)-1)/2)*
          Complex.exp ((y/4:ℝ):ℂ)*Q T h x y+
          (Complex.exp ((y/4:ℝ):ℂ)*Q T h x y-
            ((Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ))*Q T h x y)/2 := by
        simp only [Complex.ofReal_exp]
        push_cast
        ring
      _ = _ := by rw [hm];push_cast;rfl
  · rw [Set.indicator_of_notMem (by simpa using hp.le),modif_one_lt _ (by simpa using hp)]
    simp only [add_zero]
    unfold psiKernel psi
    push_cast
    ring
lemma entire_fourier_correction (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)+
      ((∫ y : ℝ in Iio 0, positiveKernel T h x y)-
        (∫ y : ℝ in Iio 0, negativeKernel T h x y))/2 := by
  rw [entire_window_fourier T h x hh,integral_congr_ae (theta_kernel_eq T h x)]
  have hi : Integrable (fun y : ℝ => (positiveKernel T h x y-negativeKernel T h x y)/2) :=
    ((positive_kernel_integrable T h x hh).sub (negative_kernel_integrable T h x hh)).div_const (2:ℂ)
  rw [integral_add (psi_kernel_integrable T h x hh) (hi.indicator measurableSet_Iio),
    integral_indicator measurableSet_Iio,integral_div,
    integral_sub (positive_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn,
    ←dirichlet_series_fourier T h x hh]
noncomputable def fullWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma full_window_eq (T h t : ℝ) :
    fullWindow T h t=entireWindow T h t-poleWindow 1 T h t-poleWindow (-1) T h t := by
  unfold fullWindow entireWindow poleWindow sline
  rw [completedRiemannZeta_eq]
  have hs : 1-(1/2+((t+T:ℝ):ℂ)*I)=1/2+(-1:ℂ)*I*((t+T:ℝ):ℂ) := by ring
  rw [hs]
  push_cast
  ring
end RHBatch01PlattFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01PlattFourier
open RHBatch01GammaFourier RHBatch01ThetaFourier RHBatch01ThetaGamma RHBatch01PoleFourier
noncomputable def modulate (f : ℝ→ℂ) (x t : ℝ) : ℂ :=
  f t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma entire_modulate_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (entireWindow T h) x) := by
  convert (theta_joint_integrable T h x hh).integral_prod_left using 1
  ext t
  simp only [thetaJoint,integral_mul_const,integral_div]
  rw [←completed_log_mellin]
  rfl
lemma pole_modulate_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (poleWindow ε T h) x) := by
  convert ((pole_joint_integrable ε T h x hh).integral_prod_left).const_mul (1/2:ℂ) using 1
  ext t
  simp only [poleJoint,integral_mul_const]
  rw [laplace_half _ (by rw [sline_re];norm_num)]
  unfold poleWindow modulate
  ring
lemma full_fourier_decomposition (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=𝓕 (entireWindow T h) x-
      𝓕 (poleWindow 1 T h) x-𝓕 (poleWindow (-1) T h) x := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  have he (t : ℝ) : Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*fullWindow T h t=
      modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t-
        modulate (poleWindow (-1) T h) x t := by
    rw [full_window_eq]
    unfold modulate
    ring
  simp_rw [he]
  have hisub : Integrable (fun t : ℝ => modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t) :=
    (entire_modulate_integrable T h x hh).sub (pole_modulate_integrable 1 T h x hh)
  rw [integral_sub hisub
    (pole_modulate_integrable (-1) T h x hh),
    integral_sub (entire_modulate_integrable T h x hh) (pole_modulate_integrable 1 T h x hh)]
  simp only [modulate,mul_comm]
lemma pole_plus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow 1 T h) x=(∫ y : ℝ in Iio 0, positiveKernel T h x y)/2 := by
  rw [pole_window_fourier 1 T h x hh]
  have he : (fun y : ℝ => Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-1*y))=
      (fun y : ℝ => positiveKernel T h x (-y)) := by
    ext y
    simp [positiveKernel]
  rw [he,integral_comp_neg_Ioi,neg_zero,integral_Iic_eq_integral_Iio]
  ring
lemma pole_minus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow (-1) T h) x=(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)/2 := by
  rw [pole_window_fourier (-1) T h x hh]
  simp only [neg_neg,one_mul]
  change (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=_
  ring
lemma full_fourier_series (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)-
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  rw [full_fourier_decomposition T h x hh,entire_fourier_correction T h x hh,
    pole_plus_fourier T h x hh,pole_minus_fourier T h x hh]
  have hi : (∫ y : ℝ in Iio 0, negativeKernel T h x y)+
      (∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=∫ y : ℝ, negativeKernel T h x y := by
    rw [←integral_Iic_eq_integral_Iio]
    exact intervalIntegral.integral_Iic_add_Ioi (negative_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn
  have hm := gaussian_pole_mass T h x hh
  change (1/2:ℂ)*(∫ y : ℝ, negativeKernel T h x y)=_ at hm
  rw [←hm,←hi]
  ring
lemma full_fourier_remainder_norm (T h x : ℝ) (hh : 0<h) :
    ‖𝓕 (fullWindow T h) x-(∑' n : Nat, dirichletTerm T h x n)‖=
      2*Real.pi*Real.exp (1/(8*h^2)-T^2/(2*h^2)-Real.pi*x) := by
  rw [full_fourier_series T h x hh]
  simp only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_exp,
    Complex.add_re,Complex.ofReal_re]
  simp
  rw [abs_of_pos Real.pi_pos]
  have he : ((T:ℂ)/(2*(h:ℂ)^2)).im=0 := by
    rw [show (T:ℂ)/(2*(h:ℂ)^2)=((T/(2*h^2):ℝ):ℂ) by push_cast;rfl]
    rfl
  rw [he,add_zero]
end RHBatch01PlattFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set
namespace RHBatch01DirichletTail
lemma power_tail (p : ℝ) (hp : 1<p) (J : Nat) (hJ : 0<J) :
    (∑' n : Nat, ((n+J+1:Nat):ℝ)^(-p))≤(J:ℝ)^(1-p)/(p-1) := by
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have ha : AntitoneOn (fun t : ℝ => t^(-p)) (Ici (J:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hJr.trans_le hx) hxy (by linarith)
  have ht := ha.tsum_comp_add_le_integral J
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hJr)
    (fun t ht => Real.rpow_nonneg (hJr.trans ht).le _)
  apply ht.trans_eq
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hJr,
    show -p+1=1-p by ring]
  rw [show 1-p= -(p-1) by ring,neg_div_neg_eq]
end RHBatch01DirichletTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01FiniteDirichlet
open RHBatch01GammaFourier RHBatch01GammaRotation RHBatch01PlattFourier RHBatch01DirichletTail
noncomputable def boundConstant (T h α : ℝ) (M : Nat) : ℝ :=
  (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
    Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/h^2)
lemma weight_norm (T a : ℝ) : ‖dirichletWeight T a‖=Real.exp (-Real.log a/2) := by
  rw [dirichletWeight,Complex.norm_exp]
  congr 1
  simp only [neg_re,mul_re,add_re,div_re,ofReal_re,ofReal_im,I_re,I_im,mul_im]
  norm_num
  ring
lemma shifted_gamma_bound (T h x α a : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (ha : 0<a) :
    ‖dirichletWeight T a*𝓕 (gammaWindow T h) (x+Real.log a/(2*Real.pi))‖ ≤
      boundConstant T h α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*a^(-(2*(M:ℝ))) := by
  rw [norm_mul,weight_norm]
  have hg := gamma_fourier_moment_bound T h (x+Real.log a/(2*Real.pi)) α M hT hh hα hα'
  apply (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans_eq
  unfold boundConstant
  rw [Real.rpow_def_of_pos ha]
  have he : -Real.log a/2+(Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
      2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*(x+Real.log a/(2*Real.pi))*(1/4-(M:ℝ)))=
      (Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/h^2)+
        4*Real.pi*x*(1/4-(M:ℝ))+Real.log a*(-(2*(M:ℝ))) := by
    field_simp [Real.pi_ne_zero]
    ring
  calc
    _ = (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*
      (Real.exp (-Real.log a/2)*Real.exp (Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
        2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*(x+Real.log a/(2*Real.pi))*(1/4-(M:ℝ)))) := by ring
    _ = _ := by rw [←Real.exp_add,he,Real.exp_add,Real.exp_add];ring
lemma dirichlet_term_bound (T h x α : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (n : Nat) :
    ‖dirichletTerm T h x n‖ ≤
      (boundConstant T h α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*Real.pi^(-(M:ℝ)))*
        (n+1:ℝ)^(-(2*(M:ℝ))) := by
  have ht := shifted_gamma_bound T h x α ((n+1:ℝ)*Real.sqrt Real.pi) M hT hh hα hα' (by positivity)
  apply ht.trans_eq
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
    ←Real.rpow_mul Real.pi_pos.le]
  rw [show (1/2:ℝ)*(-(2*(M:ℝ)))= -(M:ℝ) by ring]
  ring
lemma dirichlet_norm_summable (T h x : ℝ) (hh : 0<h) :
    Summable (fun n : Nat => ‖dirichletTerm T h x n‖) := by
  apply (RHBatch01ThetaGamma.kernel_integral_norm_summable T h x hh).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  rw [dirichlet_term_eq T h x hh]
  exact norm_integral_le_integral_norm _
end RHBatch01FiniteDirichlet
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex Finset
namespace RHBatch01DirichletMass
lemma sqrt_step (n : Nat) : (1:ℝ)/Real.sqrt (n+1:ℝ)≤2*(Real.sqrt (n+1:ℝ)-Real.sqrt (n:ℝ)) := by
  have hn:(0:ℝ)≤n := Nat.cast_nonneg n
  have hs:0<Real.sqrt (n+1:ℝ) := Real.sqrt_pos.mpr (by positivity)
  have h0:0≤Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hm:Real.sqrt (n:ℝ)≤Real.sqrt (n+1:ℝ) := Real.sqrt_le_sqrt (by linarith)
  have ha:(Real.sqrt (n+1:ℝ))^2=n+1 := Real.sq_sqrt (by positivity)
  have hb:(Real.sqrt (n:ℝ))^2=n := Real.sq_sqrt hn
  apply (div_le_iff₀ hs).mpr
  nlinarith [sq_nonneg (Real.sqrt (n+1:ℝ)-Real.sqrt (n:ℝ))]
lemma inv_sqrt_sum (N : Nat) :
    (∑ n∈Finset.range N,(1:ℝ)/Real.sqrt (n+1:ℝ))≤2*Real.sqrt (N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h:=sqrt_step N
    push_cast
    linarith
lemma weight_norm (T : ℝ) (n : Nat) :
    ‖RHBatch01GammaFourier.dirichletWeight T ((n+1:ℝ)*Real.sqrt Real.pi)‖≤1/Real.sqrt (n+1:ℝ) := by
  have hn:(0:ℝ)<n+1 := by positivity
  have hpi:1≤Real.sqrt Real.pi := (Real.one_le_sqrt).mpr (by linarith [Real.pi_gt_three])
  have hlog:Real.log (n+1:ℝ)≤Real.log ((n+1:ℝ)*Real.sqrt Real.pi) :=
    Real.log_le_log hn (by nlinarith)
  rw [RHBatch01FiniteDirichlet.weight_norm]
  calc
    _ ≤ Real.exp (-Real.log (n+1:ℝ)/2) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/Real.sqrt (n+1:ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hn,one_div,←Real.exp_neg]
      congr 1
      ring
lemma mass_50000 (T : ℝ) :
    (∑ n∈Finset.range 50000,‖RHBatch01GammaFourier.dirichletWeight T ((n+1:ℝ)*Real.sqrt Real.pi)‖)≤1000 := by
  have h:=inv_sqrt_sum 50000
  have hs:Real.sqrt (50000:ℝ)≤500 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  calc
    _ ≤ ∑ n∈Finset.range 50000,(1:ℝ)/Real.sqrt (n+1:ℝ) := Finset.sum_le_sum (fun n hn=>weight_norm T n)
    _ ≤ _ := by linarith
end RHBatch01DirichletMass
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHBatch01GammaDiscreteBudget
lemma dft_fixed {a ap b bp : Fin 16384→ℂ} {c cp : Fin 16384→Fin 16384→ℂ}
    (ha:∀ m,‖a m‖≤18) (hb:∀ m,b m=RHBatch01ChirpDFT.phase (-(m.val:ℝ)^2/16384))
    (hc:∀ n m,c n m=RHBatch01ChirpDFT.phase (((n.val:ℝ)-(m.val:ℝ))^2/16384))
    (hea:∀ m,‖a m-ap m‖≤1/10^23) (heb:∀ m,‖b m-bp m‖≤1/10^23)
    (hec:∀ n m,‖c n m-cp n m‖≤1/10^23)
    (d : ℂ) (n : Fin 16384) (hd:‖bp n*(∑ m:Fin 16384,ap m*bp m*cp n m)-d‖≤2/(2:ℝ)^80) :
    ‖RHBatch01ChirpDFT.dft a n-d‖≤1/10^16 := by
  have h:=RHBatch01ChirpDFT.dft_chirp_error a ap b bp c cp (1/10^23) (by norm_num) ha hb hc hea heb hec n
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h hd)).trans (by norm_num)
lemma fourier_fixed (p a c : Fin 16384→ℂ) (d : ℂ) (m : Fin 16384)
    (hp:∀ n,p n=((512:ℝ)⁻¹:ℂ)*∑ m:Fin 16384,
      c m*RHBatch01Fourier.phase ((m.val:ℝ)*((n.val:ℝ)-8192)/16384))
    (ht:∀ n,‖p n-a n‖≤1/10^18)
    (hd:‖RHBatch01ChirpDFT.dft a m-d‖≤1/10^16)
    (F : ℂ) (hf:‖F-c m‖≤2/10^31) :
    ‖F-RHBatch01Fourier.phase ((m.val:ℝ)/2)*((1/32:ℂ)*d)‖≤1/10^15 := by
  have h:=RHBatch01CenteredDFT.inverse_pair_error_at p a c d m 512 (-8192) (1/10^18) (1/10^16) (2/10^31)
    (by norm_num) (by intro n;convert hp n using 1 <;> congr 3 <;> ring) ht hd F hf
  have he:-(m.val:ℝ)*(-8192)/16384=(m.val:ℝ)/2 := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [he] at h
  norm_num at h ⊢
  exact h.trans (by norm_num)
end RHBatch01GammaDiscreteBudget
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open Complex Finset
open scoped ComplexConjugate
namespace RHBatch01PackedFFTSound
lemma analytic_error (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (cc:Nat→Int×Int) (r : Fin 2048)
    (a ap b bp : Fin 16384→ℂ) (c cp : Fin 16384→Fin 16384→ℂ)
    (ha:∀ m,‖a m‖≤18)
    (hb:∀ m,b m=RHBatch01ChirpDFT.phase (-(m.val:ℝ)^2/16384))
    (hc:∀ n m,c n m=RHBatch01ChirpDFT.phase (((n.val:ℝ)-(m.val:ℝ))^2/16384))
    (hea:∀ m,‖a m-ap m‖≤1/10^23)
    (heb:∀ m,‖b m-bp m‖≤1/10^23)
    (hec:∀ n m,‖c n m-cp n m‖≤1/10^23)
    (hinput:∀ j:Fin 16384,
      (((((ar j:Int)-2^166:Int):ℂ)+(((ai j:Int)-2^166:Int):ℂ)*I)/(2:ℂ)^160)=ap j*bp j)
    (hkernel:∀ j:Fin 16384,
      (((((br ⟨16383+r.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)+
        (((bi ⟨16383+r.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)*I)/(2:ℂ)^80)=cp ⟨r.val,by omega⟩ j)
    (houter:conj (pairValue (cc r.val))=bp ⟨r.val,by omega⟩) :
    ‖RHBatch01ChirpDFT.dft a ⟨r.val,by omega⟩-
      pairValue (roundPair (sumRe ar ai br bi r) (sumIm ar ai br bi r) (cc r.val))‖≤1/10^16 := by
  have h:=complex_rounding (sumRe ar ai br bi r) (sumIm ar ai br bi r) (cc r.val)
  have he:(((sumRe ar ai br bi r:ℂ)+(sumIm ar ai br bi r:ℂ)*I)/(2:ℂ)^240)*conj (pairValue (cc r.val))=
      bp ⟨r.val,by omega⟩*(∑ j:Fin 16384,ap j*bp j*cp ⟨r.val,by omega⟩ j) := by
    rw [scaled_sum,houter]
    simp_rw [hinput,hkernel]
    ring
  rw [he] at h
  exact RHBatch01GammaDiscreteBudget.dft_fixed ha hb hc hea heb hec _ ⟨r.val,by omega⟩ h
end RHBatch01PackedFFTSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex CauSeq Finset
namespace RHBatch01Taylor
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
end RHBatch01Taylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GaussianTaylor
open RHBatch01GammaFourier RHBatch01Taylor
lemma gamma_window_norm (T h t : ℝ) : ‖gammaWindow T h t‖≤6*Real.exp (-t^2/(2*h^2)) := by
  have h := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t h 0
  simpa only [pow_zero,mul_one,one_mul,gammaWindow,window,Complex.ofReal_exp] using h
lemma pow_exp_factorial (v : ℝ) (hv : 0≤v) (n : Nat) :
    v^n*Real.exp (-v)≤(n.factorial:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp v hv n
  rw [div_le_iff₀ (show (0:ℝ)<n.factorial by positivity)] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-v)).le
  have he : Real.exp v*(n.factorial:ℝ)*Real.exp (-v)=(n.factorial:ℝ) := by
    calc
      _ = n.factorial*(Real.exp v*Real.exp (-v)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  simpa only [he] using hm
lemma young_gaussian (t : ℝ) :
    Real.exp (-t^2/800+|t|/128)≤3*Real.exp (-t^2/1600) := by
  have hy : -t^2/800+|t|/128≤1-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-25/4)]
  calc
    _ ≤ Real.exp (1-t^2/1600) := Real.exp_le_exp.mpr hy
    _ = Real.exp 1*Real.exp (-t^2/1600) := by rw [sub_eq_add_neg,Real.exp_add,neg_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
lemma polynomial_gaussian (t : ℝ) :
    |t|^20*Real.exp (-t^2/1600)≤
      (3200:ℝ)^10*((10).factorial:ℝ)*Real.exp (-t^2/3200) := by
  have hp := pow_exp_factorial (t^2/3200) (by positivity) 10
  have he : |t|^20=(3200:ℝ)^10*(t^2/3200)^10 := by
    rw [show (20:Nat)=2*10 by norm_num,pow_mul,sq_abs]
    ring
  have he' : -t^2/1600= -t^2/3200+(-t^2/3200) := by ring
  rw [he,he',Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-t^2/3200)).le)
    (show 0≤(3200:ℝ)^10 by positivity)
  convert hm using 1 <;> first | rfl | ring
noncomputable def remainder (T δ t : ℝ) : ℂ :=
  gammaWindow T 20 t*(Complex.exp (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)-
    ∑ k ∈ Finset.range 20, (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)^k/(k.factorial:ℂ))
noncomputable def constant : ℝ :=
  18*(1/128:ℝ)^20*(3200:ℝ)^10*((10).factorial:ℝ)/((20).factorial:ℝ)
lemma remainder_norm (T δ t : ℝ) (hδ : |δ|≤1/1024) :
    ‖remainder T δ t‖ ≤ constant*Real.exp (-t^2/3200) := by
  let z : ℂ := -2*(Real.pi:ℂ)*I*(δ:ℂ)*t
  have hn : ‖z‖≤|t|/128 := by
    dsimp [z]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,norm_neg,
      norm_ofNat,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_lt_four,Real.pi_pos,abs_nonneg δ,abs_nonneg t,
      mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hδ),
      mul_nonneg (abs_nonneg δ) (sub_nonneg.mpr Real.pi_lt_four.le)]
  have hg := gamma_window_norm T 20 t
  norm_num at hg
  have hr := exp_factorial_remainder z 20
  have hz : ‖remainder T δ t‖=‖gammaWindow T 20 t‖*
      ‖Complex.exp z-∑ k ∈ Finset.range 20, z^k/(k.factorial:ℂ)‖ := by rw [remainder,norm_mul]
  rw [hz]
  calc
    _ ≤ (6*Real.exp (-t^2/800))*((|t|/128)^20/((20).factorial:ℝ)*Real.exp (|t|/128)) := by
      apply mul_le_mul hg _ (norm_nonneg _) (by positivity)
      apply hr.trans
      gcongr
    _ = (6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20*
        Real.exp (-t^2/800+|t|/128) := by rw [Real.exp_add];ring
    _ ≤ (18*(1/128:ℝ)^20/((20).factorial:ℝ))*(|t|^20*Real.exp (-t^2/1600)) := by
      have hm := mul_le_mul_of_nonneg_left (young_gaussian t)
        (show 0≤(6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20 by positivity)
      convert hm using 1 <;> first | rfl | ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left (polynomial_gaussian t)
        (show 0≤18*(1/128:ℝ)^20/((20).factorial:ℝ) by positivity)
      convert hm using 1 <;> first | rfl | (simp only [constant];ring)
end RHBatch01GaussianTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GaussianTaylor
open RHBatch01GammaFourier
lemma gamma_window_continuous (T h : ℝ) : Continuous (gammaWindow T h) := by
  have hc : Continuous (fun t : ℝ => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro m hm
      have hz : 0<(1/4+(((t+T)/2:ℝ):ℂ)*I).re := by simp
      rw [hm] at hz
      have hmr : (0:ℝ) ≤ m := by positivity
      simp only [neg_re,natCast_re] at hz
      linarith
  have hw : Continuous (window T h) := by unfold window;fun_prop
  exact hc.mul hw
lemma remainder_continuous (T δ : ℝ) : Continuous (remainder T δ) := by
  have hg := gamma_window_continuous T 20
  unfold remainder
  apply hg.mul
  fun_prop
lemma gaussian_bound_integrable : Integrable (fun t : ℝ => Real.exp (-t^2/3200)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/3200) using 1
  ext t
  congr 1
  ring
lemma remainder_integrable (T δ : ℝ) (hδ : |δ|≤1/1024) : Integrable (remainder T δ) := by
  apply (gaussian_bound_integrable.const_mul constant).mono' (remainder_continuous T δ).aestronglyMeasurable
  filter_upwards [] with t
  exact remainder_norm T δ t hδ
lemma gaussian_mass_le : (∫ t : ℝ, Real.exp (-t^2/3200))≤120 := by
  have he : (fun t : ℝ => Real.exp (-t^2/3200))=(fun t : ℝ => Real.exp (-(1/3200:ℝ)*t^2)) := by
    ext t
    congr 1
    ring
  rw [he,integral_gaussian]
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · norm_num
    nlinarith [Real.pi_lt_four]
lemma constant_mass_small : constant*120≤1/10^15 := by
  norm_num [constant,Nat.factorial]
lemma modulated_remainder_integral (T δ x : ℝ) (hδ : |δ|≤1/1024) :
    ‖∫ t : ℝ, remainder T δ t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)‖≤1/10^15 := by
  have hc : 0≤constant := by unfold constant;positivity
  have hb : ∀ᵐ t : ℝ ∂volume,
      ‖remainder T δ t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)‖≤constant*Real.exp (-t^2/3200) := by
    filter_upwards [] with t
    rw [norm_mul,Complex.norm_exp]
    have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
    rw [he,Real.exp_zero,mul_one]
    exact remainder_norm T δ t hδ
  calc
    _ ≤ ∫ t : ℝ, constant*Real.exp (-t^2/3200) :=
      norm_integral_le_of_norm_le (gaussian_bound_integrable.const_mul constant) hb
    _ = constant*(∫ t : ℝ, Real.exp (-t^2/3200)) := integral_const_mul _ _
    _ ≤ constant*120 := mul_le_mul_of_nonneg_left gaussian_mass_le hc
    _ ≤ _ := constant_mass_small
end RHBatch01GaussianTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaTaylorFourier
open RHBatch01GammaFourier RHBatch01GaussianTaylor
noncomputable def phase (x t : ℝ) : ℂ := Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma phase_norm (x t : ℝ) : ‖phase x t‖=1 := by simp [phase,Complex.norm_exp]
lemma modulate_integrable (f : ℝ→ℂ) (hf : Integrable f) (x : ℝ) :
    Integrable (fun t : ℝ => f t*phase x t) := by
  apply hf.norm.mono'
  · have hc : Continuous (phase x) := by unfold phase;fun_prop
    exact hf.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul,phase_norm,mul_one]
lemma fourier_eq (f : ℝ→ℂ) (x : ℝ) : 𝓕 f x=∫ t : ℝ, f t*phase x t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,phase,mul_comm]
noncomputable def moment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  gammaWindow T 20 t*(-2*(Real.pi:ℂ)*I*(t:ℂ))^k
lemma moment_integrable (T : ℝ) (k : Nat) : Integrable (moment T k) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b:=(1/800:ℝ)) (by norm_num)
    (s:=(k:ℝ)) (by
      have hk : (0:ℝ)≤k := by positivity
      linarith)
  have hi' : Integrable (fun t : ℝ => |t|^k*Real.exp (-t^2/800)) := by
    convert hi.norm using 1
    ext t
    rw [Real.norm_eq_abs,abs_mul,Real.rpow_natCast,abs_pow,abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  have hc : Continuous (moment T k) := by
    have hg := gamma_window_continuous T 20
    unfold moment
    fun_prop
  apply (hi'.const_mul (6*(2*Real.pi)^k)).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t 20 k
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at hg
  simpa only [moment,gammaWindow,window,show (2*(20:ℝ)^2)=800 by norm_num,
    Complex.ofReal_exp,mul_pow,mul_assoc] using hg
noncomputable def polynomial (T δ t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*moment T k t
lemma polynomial_integrable (T δ : ℝ) : Integrable (polynomial T δ) := by
  exact integrable_finsetSum _ (fun k hk => (moment_integrable T k).const_mul _)
lemma remainder_eq (T δ t : ℝ) :
    remainder T δ t=gammaWindow T 20 t*phase δ t-polynomial T δ t := by
  unfold remainder phase polynomial moment
  rw [mul_sub,Finset.mul_sum]
  congr 1
  · congr 2
    push_cast
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    have he : -2*(Real.pi:ℂ)*I*(δ:ℂ)*t=(δ:ℂ)*(-2*(Real.pi:ℂ)*I*(t:ℂ)) := by ring
    rw [he,mul_pow]
    ring
lemma shifted_fourier (T δ x : ℝ) :
    𝓕 (gammaWindow T 20) (x+δ)=𝓕 (fun t : ℝ => gammaWindow T 20 t*phase δ t) x := by
  rw [fourier_eq,fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold phase
  conv_rhs => rw [mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
lemma polynomial_fourier (T δ x : ℝ) :
    𝓕 (polynomial T δ) x=
      ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*𝓕 (moment T k) x := by
  rw [fourier_eq]
  simp only [polynomial,Finset.sum_mul]
  simp only [mul_assoc]
  rw [integral_finsetSum _ (fun k hk =>
    (modulate_integrable (moment T k) (moment_integrable T k) x).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_eq,←integral_const_mul]
lemma fourier_taylor_error (T δ x : ℝ) (hδ : |δ|≤1/1024) :
    ‖𝓕 (gammaWindow T 20) (x+δ)-
      ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*𝓕 (moment T k) x‖≤1/10^15 := by
  have hg : Integrable (gammaWindow T 20) := by
    convert moment_integrable T 0 using 1
    ext t
    simp [moment]
  rw [shifted_fourier,←polynomial_fourier,fourier_eq,fourier_eq]
  rw [←integral_sub (modulate_integrable _ (modulate_integrable _ hg δ) x)
    (modulate_integrable _ (polynomial_integrable T δ) x)]
  have he : (fun t : ℝ => (gammaWindow T 20 t*phase δ t)*phase x t-polynomial T δ t*phase x t)=
      (fun t : ℝ => remainder T δ t*phase x t) := by
    ext t
    rw [remainder_eq]
    ring
  rw [he]
  exact modulated_remainder_integral T δ x hδ
end RHBatch01GammaTaylorFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaTimeTail
open RHBatch01GammaFourier RHBatch01GammaTaylorFourier
noncomputable def scaledMoment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  moment T k t/((k.factorial:ℂ)*(512:ℂ)^k)
lemma scaled_moment_norm (T t : ℝ) (k : Nat) :
    ‖scaledMoment T k t‖≤6*Real.exp (|t|/64-t^2/800) := by
  have hd : (0:ℝ)<(k.factorial:ℝ)*(512:ℝ)^k := by positivity
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t 20 k
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at hg
  have hbase : ‖moment T k t‖≤6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800) := by
    simpa only [moment,gammaWindow,window,Complex.ofReal_exp,
      show (2*(20:ℝ)^2)=800 by norm_num] using hg
  rw [scaledMoment,norm_div,norm_mul,norm_natCast,norm_pow,norm_ofNat]
  apply (div_le_div_of_nonneg_right hbase hd.le).trans
  have he : (6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800))/((k.factorial:ℝ)*512^k)=
      6*((Real.pi*|t|/256)^k/(k.factorial:ℝ))*Real.exp (-t^2/800) := by
    rw [div_pow]
    field_simp
    rw [show (512:ℝ)^k=(2:ℝ)^k*256^k by rw [←mul_pow];norm_num]
    ring
  rw [he]
  have hp := Real.pow_div_factorial_le_exp (Real.pi*|t|/256) (by positivity) k
  have hu : Real.pi*|t|/256≤|t|/64 := by nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr Real.pi_lt_four.le)]
  calc
    _ ≤ 6*Real.exp (Real.pi*|t|/256)*Real.exp (-t^2/800) := by gcongr
    _ ≤ 6*Real.exp (|t|/64)*Real.exp (-t^2/800) := by gcongr
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
lemma scaled_moment_tail (T t : ℝ) (k : Nat) (ht : 256≤|t|) :
    ‖scaledMoment T k t‖≤6*Real.exp (-|t|/4) := by
  apply (scaled_moment_norm T t k).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs t,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
lemma positive_alias_term (T t : ℝ) (k n : Nat) (ht : -256≤t) :
    ‖scaledMoment T k (t+(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : 256≤t+(n+1:ℝ)*512 := by linarith
  have habs : |t+(n+1:ℝ)*512|=t+(n+1:ℝ)*512 := abs_of_nonneg (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];exact ha)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
lemma negative_alias_term (T t : ℝ) (k n : Nat) (ht : t≤256) :
    ‖scaledMoment T k (t-(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : t-(n+1:ℝ)*512≤ -256 := by linarith
  have habs : |t-(n+1:ℝ)*512|= -(t-(n+1:ℝ)*512) := abs_of_nonpos (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];linarith)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
end RHBatch01GammaTimeTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace RHBatch01GammaTimeTail
lemma scaled_moment_gaussian (T t : ℝ) (k : Nat) :
    ‖scaledMoment T k t‖≤18*Real.exp (-t^2/1600) := by
  have hy : |t|/64-t^2/800≤1-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-25/2)]
  calc
    _ ≤ 6*Real.exp (|t|/64-t^2/800) := scaled_moment_norm T t k
    _ ≤ 6*Real.exp (1-t^2/1600) := by gcongr
    _ = (6*Real.exp 1)*Real.exp (-t^2/1600) := by rw [sub_eq_add_neg,Real.exp_add,neg_div,mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.exp_one_lt_three]
lemma scaled_moment_continuous (T : ℝ) (k : Nat) : Continuous (scaledMoment T k) := by
  have hg := RHBatch01GaussianTaylor.gamma_window_continuous T 20
  unfold scaledMoment RHBatch01GammaTaylorFourier.moment
  fun_prop
lemma scaled_moment_rpow_decay (T : ℝ) (k : Nat) :
    (scaledMoment T k)=O[cocompact ℝ] (fun t : ℝ => |t|^(-(2:ℝ))) := by
  let g : ℝ→ℂ := fun t => Complex.exp (-(1/1600:ℂ)*(t:ℂ)^2)
  have hg : (scaledMoment T k)=O[cocompact ℝ] g := by
    apply isBigO_iff.mpr
    refine ⟨18,Eventually.of_forall (fun t => ?_)⟩
    change ‖scaledMoment T k t‖≤18*‖Complex.exp (-(1/1600:ℂ)*(t:ℂ)^2)‖
    rw [norm_cexp_neg_mul_sq]
    norm_num
    convert scaled_moment_gaussian T t k using 1 <;> congr 2 <;> ring
  have he := (isLittleO_exp_neg_mul_sq_cocompact (a:=(1/1600:ℂ))
    (by norm_num) (-(2:ℝ))).isBigO
  exact hg.trans he
end RHBatch01GammaTimeTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighSamplingFunctions
open _root_.RHHighSamplingFunctions
lemma moment_eq (T t : ℝ) (k : Nat) : moment T k t=RHBatch01GammaTimeTail.scaledMoment T k t := by
  unfold moment gammaWindow RHBatch01GammaTimeTail.scaledMoment RHBatch01GammaTaylorFourier.moment
    RHBatch01GammaFourier.gammaWindow RHBatch01GammaFourier.window
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num]
lemma moment_norm (T t : ℝ) (k : Nat) : ‖moment T k t‖≤18 := by
  rw [moment_eq]
  apply (RHBatch01GammaTimeTail.scaled_moment_gaussian T t k).trans
  have h:Real.exp (-t^2/1600)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  nlinarith
end RHHighSamplingFunctions
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
open scoped ComplexConjugate
namespace RHBatch01IndexedChirpAccuracy
noncomputable def value (j : Nat) : ℂ :=
  let v:=RHHighFFTArithmeticBase.chirp j
  ((v.1:ℂ)+(v.2:ℂ)*I)/(2:ℂ)^80
lemma phase_period (x : ℝ) (k : Nat) : RHBatch01ChirpDFT.phase (x+2*(k:ℝ))=RHBatch01ChirpDFT.phase x := by
  unfold RHBatch01ChirpDFT.phase
  have he:((Real.pi*(x+2*(k:ℝ)):ℝ):ℂ)*I=
    ((Real.pi*x:ℝ):ℂ)*I+(k:ℂ)*(2*(Real.pi:ℂ)*I) := by push_cast;ring
  rw [he,Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,mul_one]
lemma phase_conj (x : ℝ) : conj (RHBatch01ChirpDFT.phase x)=RHBatch01ChirpDFT.phase (-x) := by
  unfold RHBatch01ChirpDFT.phase
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring
lemma reduced (j : Nat) :
    RHBatch01ChirpDFT.phase ((j:ℝ)^2/16384)=RHBatch01ChirpDFT.phase ((j*j%32768:Nat)/16384:ℝ) := by
  have h:=Nat.mod_add_div (j*j) 32768
  have hr:((j*j%32768:Nat):ℝ)+32768*((j*j/32768:Nat):ℝ)=(j:ℝ)^2 := by rw [pow_two];exact_mod_cast h
  rw [show (j:ℝ)^2/16384=((j*j%32768:Nat):ℝ)/16384+2*((j*j/32768:Nat):ℝ) by linarith]
  exact phase_period _ _
noncomputable def covered : Bool := (List.range 32767).all (fun j =>
  RHHighChirpCache.needed (min (j*j%32768) (32768-j*j%32768)))
theorem covered_checked : covered=true := by decide +kernel
lemma enclosure (j : Nat) (hj:j<32767) :
    ‖value j-RHBatch01ChirpDFT.phase ((j:ℝ)^2/16384)‖≤1/10^23 := by
  let q:=j*j%32768
  let m:=min q (32768-q)
  have hq:q<32768:=Nat.mod_lt _ (by decide)
  have hm:m≤16384:=by dsimp only [m];omega
  have hneeded:RHHighChirpCache.needed m=true:=
    (List.all_eq_true.mp covered_checked) j (List.mem_range.mpr hj)
  let v:RHHighChirpCache.Record:=(RHHighChirpCache.expected[m]?).getD ⟨0,0,0,0⟩
  have h:=TaoFivePrimes.rh_high_height_chirp_enclosures_16384 m hm hneeded
  change ‖((v.r:ℂ)+(v.i:ℂ)*I)/(2:ℂ)^80-
    Complex.exp (I*((Real.pi*(m:ℝ)/16384:ℝ):ℂ))‖≤1/10^23 at h
  have hp:Complex.exp (I*((Real.pi*(m:ℝ)/16384:ℝ):ℂ))=RHBatch01ChirpDFT.phase ((m:ℝ)/16384) := by
    unfold RHBatch01ChirpDFT.phase
    congr 1
    push_cast
    ring
  rw [hp] at h
  rw [reduced]
  unfold value RHHighFFTArithmeticBase.chirp
  change ‖(((RHHighChirpIndexed.lookup m).r:ℂ)+
    ((if q>16384 then -(RHHighChirpIndexed.lookup m).i else (RHHighChirpIndexed.lookup m).i: Int):ℂ)*I)/(2:ℂ)^80-
      RHBatch01ChirpDFT.phase ((q:ℝ)/16384)‖≤1/10^23
  rw [RHHighChirpIndexed.lookup_eq]
  by_cases hq':q>16384
  · have hm':m=32768-q:=by dsimp [m];omega
    have he:((q:ℝ)/16384)= -((m:ℝ)/16384)+2 := by rw [hm',Nat.cast_sub hq.le];push_cast;ring
    rw [he,show (2:ℝ)=2*(1:Nat) by norm_num,phase_period]
    have hc:=h
    rw [←Complex.norm_conj, map_sub,phase_conj] at hc
    simpa only [hq',if_true,map_div₀,map_add,map_mul,map_pow,map_intCast,
      Complex.conj_I,Complex.conj_ofNat,Int.cast_neg,mul_neg,neg_mul,sub_eq_add_neg,v] using hc
  · have hm':m=q:=by dsimp [m];omega
    simpa only [hq',if_false,hm',v] using h
end RHBatch01IndexedChirpAccuracy
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaComplexFourier
open RHBatch01GammaFourier RHBatch01GammaRotation
noncomputable def transform (T h : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, gammaWindow T h t*Complex.exp (-2*(Real.pi:ℂ)*I*z*t)
lemma transform_real (T h x : ℝ) : transform T h (x:ℂ)=𝓕 (gammaWindow T h) x := by
  rw [transform,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  have he : -2*(Real.pi:ℂ)*I*(x:ℂ)*t=(((-2*Real.pi*t*x:ℝ):ℂ)*I) := by push_cast;ring
  rw [he,mul_comm]
lemma transform_complex_shift (T h x v : ℝ) (hh : 0<h) :
    transform T h ((x:ℂ)+(v:ℂ)*I)=
      Complex.exp (((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-
        I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))*
          𝓕 (gammaWindow (T+2*Real.pi*h^2*v) h) x := by
  let m : ℝ := 2*Real.pi*h^2*v
  rw [transform]
  rw [←integral_add_right_eq_self (μ:=(volume:Measure ℝ))
    (fun t : ℝ => gammaWindow T h t*Complex.exp (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*t)) m]
  rw [Real.fourier_real_eq_integral_exp_smul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  unfold gammaWindow window
  have harg : (((t+m+T)/2:ℝ):ℂ)=(((t+(T+2*Real.pi*h^2*v))/2:ℝ):ℂ) := by
    dsimp [m]
    congr 1
    ring
  rw [harg]
  have he : ((Real.pi*(t+m+T)/4-(t+m)^2/(2*h^2):ℝ):ℂ)+
      (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*(t+m))=
      (((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))+
        (((-2*Real.pi*t*x:ℝ):ℂ)*I)+
        ((Real.pi*(t+(T+2*Real.pi*h^2*v))/4-t^2/(2*h^2):ℝ):ℂ) := by
    dsimp [m]
    push_cast
    have hn : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
    field_simp [hn]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  calc
    _ = Complex.Gamma (1/4+(((t+(T+2*Real.pi*h^2*v))/2:ℝ):ℂ)*I)*
      Complex.exp (((Real.pi*(t+m+T)/4-(t+m)^2/(2*h^2):ℝ):ℂ)+
        (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*(t+m))) := by rw [Complex.exp_add];push_cast;ring
    _ = _ := by rw [he,Complex.exp_add,Complex.exp_add];push_cast;ring
lemma transform_complex_negative_bound (T h x v : ℝ) (hh : 0<h)
    (hT : 0≤T+2*Real.pi*h^2*v) :
    ‖transform T h ((x:ℂ)+(v:ℂ)*I)‖ ≤
      4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)+2*Real.pi^2*h^2*v^2) := by
  rw [transform_complex_shift T h x v hh,norm_mul,Complex.norm_exp]
  have he : ((((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))).re=
      2*Real.pi^2*h^2*v^2 := by
    simp only [sub_re,ofReal_re,mul_re,mul_im,I_re,I_im,ofReal_im,mul_zero,
      zero_mul,zero_add,sub_zero]
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (gamma_fourier_negative_bound (T+2*Real.pi*h^2*v) h x hT hh)
    (Real.exp_pos (2*Real.pi^2*h^2*v^2)).le
  apply hb.trans_eq
  calc
    _ = 4*Real.pi*(Real.exp (2*Real.pi^2*h^2*v^2)*Real.exp (Real.pi*x+1/(8*h^2))) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring
end RHBatch01GammaComplexFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01GammaCircle
open RHBatch01GammaFourier RHBatch01GammaComplexFourier RHBatch01GammaTaylorFourier RHBatch01GaussianTaylor
noncomputable def joint (T x r : ℝ) (k : Nat) (θ t : ℝ) : ℂ :=
  (deriv (circleMap (x:ℂ) r) θ/((circleMap (x:ℂ) r θ-(x:ℂ))^(k+1)))*
    gammaWindow T 20 t*Complex.exp (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t)
lemma circle_sub_norm (x r θ : ℝ) (hr : 0<r) :
    ‖circleMap (x:ℂ) r θ-(x:ℂ)‖=r := by
  rw [circleMap_sub_center,norm_circleMap_zero,abs_of_pos hr]
lemma circle_sub_ne (x r θ : ℝ) (hr : 0<r) :
    circleMap (x:ℂ) r θ-(x:ℂ)≠0 := by
  apply norm_pos_iff.mp
  rw [circle_sub_norm x r θ hr]
  exact hr
lemma circle_im_le (x r θ : ℝ) (hr : 0<r) : |(circleMap (x:ℂ) r θ).im|≤r := by
  have h := Complex.abs_im_le_norm (circleMap (x:ℂ) r θ-(x:ℂ))
  simpa only [sub_im,ofReal_im,sub_zero,circle_sub_norm x r θ hr] using h
lemma joint_norm_le (T x r θ t : ℝ) (k : Nat) (hr : 0<r) :
    ‖joint T x r k θ t‖ ≤
      ((6/r^k)*Real.exp (1600*Real.pi^2*r^2))*Real.exp (-t^2/1600) := by
  rw [joint,norm_mul,norm_mul,norm_div,deriv_circleMap,norm_mul,norm_I,mul_one,
    norm_circleMap_zero,abs_of_pos hr,norm_pow,circle_sub_norm x r θ hr,Complex.norm_exp]
  have he : (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t).re=
      2*Real.pi*(circleMap (x:ℂ) r θ).im*t := by
    simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,
      mul_one,one_mul,sub_zero,zero_sub,neg_re,neg_im]
    norm_num
  rw [he]
  have hph : 2*Real.pi*(circleMap (x:ℂ) r θ).im*t≤2*Real.pi*r*|t| := by
    have hi := circle_im_le x r θ hr
    have hab := le_abs_self ((circleMap (x:ℂ) r θ).im*t)
    rw [abs_mul] at hab
    have hm := mul_le_mul_of_nonneg_right hi (abs_nonneg t)
    nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left (hab.trans hm) Real.pi_pos.le]
  have hy : -t^2/800+2*Real.pi*r*|t|≤1600*Real.pi^2*r^2-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-1600*Real.pi*r)]
  have hg := gamma_window_norm T 20 t
  norm_num at hg
  have hquot : r/r^(k+1)=1/r^k := by rw [pow_succ];field_simp [hr.ne']
  rw [hquot]
  calc
    _ ≤ (1/r^k)*(6*Real.exp (-t^2/800))*Real.exp (2*Real.pi*r*|t|) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (Real.exp_le_exp.mpr hph) (Real.exp_pos _).le (by positivity)
    _ = (6/r^k)*Real.exp (-t^2/800+2*Real.pi*r*|t|) := by rw [Real.exp_add];ring
    _ ≤ (6/r^k)*Real.exp (1600*Real.pi^2*r^2-t^2/1600) := by gcongr
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,neg_div];ring
lemma joint_continuous (T x r : ℝ) (k : Nat) (hr : 0<r) :
    Continuous (fun p : ℝ×ℝ => joint T x r k p.1 p.2) := by
  have hc : Continuous (fun θ : ℝ => deriv (circleMap (x:ℂ) r) θ/
      (circleMap (x:ℂ) r θ-(x:ℂ))^(k+1)) := by
    simp only [deriv_circleMap]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      exact pow_ne_zero _ (circle_sub_ne x r θ hr)
  have hg : Continuous (fun p : ℝ×ℝ => gammaWindow T 20 p.2) :=
    (gamma_window_continuous T 20).comp continuous_snd
  have he : Continuous (fun p : ℝ×ℝ => Complex.exp (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r p.1)*p.2)) := by fun_prop
  exact ((hc.comp continuous_fst).mul hg).mul he
lemma joint_integrable (T x r : ℝ) (k : Nat) (hr : 0<r) :
    Integrable (fun p : ℝ×ℝ => joint T x r k p.1 p.2)
      ((volume.restrict (Icc 0 (2*Real.pi))).prod volume) := by
  have hθ : IntegrableOn (fun θ : ℝ => (1:ℝ)) (Icc 0 (2*Real.pi)) :=
    continuous_const.integrableOn_Icc
  have ht : Integrable (fun t : ℝ => Real.exp (-t^2/1600)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/1600) using 1
    ext t
    congr 1
    ring
  have hm := hθ.mul_prod (ht.const_mul ((6/r^k)*Real.exp (1600*Real.pi^2*r^2)))
  apply hm.mono' (joint_continuous T x r k hr).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [one_mul] using joint_norm_le T x r p.1 p.2 k hr
end RHBatch01GammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01GammaCircle
open RHBatch01GammaFourier RHBatch01GammaComplexFourier RHBatch01GammaTaylorFourier RHBatch01GaussianTaylor
lemma circle_exp_coefficient (a c : ℂ) (r : ℝ) (hr : 0<r) (k : Nat) :
    (∮ z in C(c,r), (1/(z-c)^(k+1))*Complex.exp (a*z))=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*(a^k*Complex.exp (a*c)) := by
  have hd : Differentiable ℂ (fun z : ℂ => Complex.exp (a*z)) := by fun_prop
  have h := hd.diffContOnCl.circleIntegral_one_div_sub_center_pow_smul (c:=c) hr k
  simpa only [smul_eq_mul,iteratedDeriv_cexp_const_mul] using h
lemma joint_inner (T x r t : ℝ) (k : Nat) (hr : 0<r) :
    (∫ θ : ℝ in Icc 0 (2*Real.pi), joint T x r k θ t)=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*(moment T k t*phase x t) := by
  let a : ℂ := -2*(Real.pi:ℂ)*I*(t:ℂ)
  have he : (∫ θ : ℝ in Icc 0 (2*Real.pi), joint T x r k θ t)=
      ∮ z in C((x:ℂ),r), gammaWindow T 20 t*((1/(z-(x:ℂ))^(k+1))*Complex.exp (a*z)) := by
    rw [circleIntegral_def_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    dsimp [joint]
    have hexp : -2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t=a*(circleMap (x:ℂ) r θ) := by dsimp [a];ring
    rw [hexp]
    ring
  rw [he]
  have hm := circleIntegral.integral_smul (gammaWindow T 20 t)
    (fun z : ℂ => (1/(z-(x:ℂ))^(k+1))*Complex.exp (a*z)) (x:ℂ) r
  simp only [smul_eq_mul] at hm
  rw [hm,circle_exp_coefficient a (x:ℂ) r hr k]
  have hexp : a*(x:ℂ)=(((-2*Real.pi*t*x:ℝ):ℂ)*I) := by dsimp [a];push_cast;ring
  rw [hexp]
  unfold moment phase
  dsimp [a]
  ring
lemma circle_transform_eq (T x r : ℝ) (k : Nat) (hr : 0<r) :
    (∮ z in C((x:ℂ),r), (1/(z-(x:ℂ))^(k+1))*transform T 20 z)=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*𝓕 (moment T k) x := by
  have he : (∮ z in C((x:ℂ),r), (1/(z-(x:ℂ))^(k+1))*transform T 20 z)=
      ∫ θ : ℝ in Icc 0 (2*Real.pi), ∫ t : ℝ, joint T x r k θ t := by
    rw [circleIntegral_def_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    unfold transform
    simp only [joint,smul_eq_mul,mul_assoc,integral_const_mul]
    ring
  rw [he,integral_integral_swap (joint_integrable T x r k hr)]
  simp_rw [joint_inner T x r _ k hr]
  rw [integral_const_mul,fourier_eq]
lemma moment_fourier_cauchy (T x r M : ℝ) (k : Nat) (hr : 0<r)
    (hM : ∀ z ∈ sphere (x:ℂ) r, ‖transform T 20 z‖≤M) :
    ‖𝓕 (moment T k) x‖/(k.factorial:ℝ)≤M/r^k := by
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f:=fun z : ℂ => (1/(z-(x:ℂ))^(k+1))*transform T 20 z) hr.le
    (C:=M/r^(k+1)) (fun z hz => by
      rw [norm_mul,norm_div,norm_one,norm_pow,(mem_sphere_iff_norm.mp hz)]
      exact (mul_le_mul_of_nonneg_left (hM z hz) (by positivity)).trans_eq (by ring))
  rw [circle_transform_eq T x r k hr,smul_eq_mul] at hb
  have he : (2*(Real.pi:ℂ)*I)⁻¹*((2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*𝓕 (moment T k) x)=
      𝓕 (moment T k) x/(k.factorial:ℂ) := by
    field_simp [Real.pi_ne_zero,Complex.I_ne_zero,show (k.factorial:ℂ)≠0 by exact_mod_cast k.factorial_ne_zero]
  rw [he,norm_div,norm_natCast] at hb
  have hpow : r*(M/r^(k+1))=M/r^k := by rw [pow_succ];field_simp [hr.ne'] <;> ring
  simpa only [hpow] using hb
end RHBatch01GammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01GammaCircle
open RHBatch01GammaFourier RHBatch01GammaComplexFourier RHBatch01GammaTaylorFourier
noncomputable def radius : ℝ := 1/(40*Real.pi)
lemma radius_pos : 0<radius := by unfold radius;positivity
lemma radius_pi : Real.pi*radius=1/40 := by unfold radius;field_simp
lemma radius_quadratic : 800*Real.pi^2*radius^2=1/2 := by
  unfold radius
  field_simp
  ring
lemma transform_sphere_bound (T x : ℝ) (hT : 20≤T) :
    ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖≤12*Real.pi*Real.exp (Real.pi*x) := by
  intro z hz
  have hn : ‖z-(x:ℂ)‖=radius := mem_sphere_iff_norm.mp hz
  have hi : |z.im|≤radius := by
    simpa only [sub_im,ofReal_im,sub_zero,hn] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hr : z.re≤x+radius := by
    have he := Complex.re_le_norm (z-(x:ℂ))
    simp only [sub_re,ofReal_re,hn] at he
    linarith
  have hv : 0≤T+2*Real.pi*(20:ℝ)^2*z.im := by
    have he := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (by positivity : 0≤800*Real.pi)
    have hp : 800*Real.pi*radius=20 := by rw [mul_assoc,radius_pi];norm_num
    nlinarith
  have hg := transform_complex_negative_bound T 20 z.re z.im (by norm_num) hv
  rw [Complex.re_add_im] at hg
  have he : Real.pi*z.re+1/(8*(20:ℝ)^2)+2*Real.pi^2*(20:ℝ)^2*z.im^2≤Real.pi*x+1 := by
    have hi2 : z.im^2≤radius^2 := by
      have hs := (sq_le_sq₀ (abs_nonneg z.im) radius_pos.le).mpr hi
      simpa only [sq_abs] using hs
    have hre := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
    have hime := mul_le_mul_of_nonneg_left hi2 (by positivity : 0≤800*Real.pi^2)
    rw [radius_quadratic] at hime
    rw [mul_add,radius_pi] at hre
    nlinarith
  calc
    _ ≤ 4*Real.pi*Real.exp (Real.pi*z.re+1/(8*(20:ℝ)^2)+2*Real.pi^2*(20:ℝ)^2*z.im^2) := hg
    _ ≤ 4*Real.pi*Real.exp (Real.pi*x+1) := by gcongr
    _ = (4*Real.pi*Real.exp (Real.pi*x))*Real.exp 1 := by rw [Real.exp_add];ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
        (show 0≤4*Real.pi*Real.exp (Real.pi*x) by positivity)
      convert hm using 1 <;> first | rfl | ring
lemma moment_negative_bound (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (moment T k) x‖/((k.factorial:ℝ)*(512:ℝ)^k)≤
      (12*Real.pi*Real.exp (Real.pi*x))*(5/16:ℝ)^k := by
  have hc := moment_fourier_cauchy T x radius (12*Real.pi*Real.exp (Real.pi*x)) k radius_pos
    (transform_sphere_bound T x hT)
  have hb := div_le_div_of_nonneg_right hc (show 0≤(512:ℝ)^k by positivity)
  have he : (12*Real.pi*Real.exp (Real.pi*x)/radius^k)/(512:ℝ)^k=
      (12*Real.pi*Real.exp (Real.pi*x))*(40*Real.pi/512)^k := by
    unfold radius
    rw [div_pow]
    field_simp [Real.pi_ne_zero]
    rw [div_pow,one_pow]
    field_simp
  rw [←div_mul_eq_div_div,he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Real.pi_lt_four]
end RHBatch01GammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaComplexFourier
open RHBatch01GammaFourier RHBatch01GammaRotation RHBatch01FiniteDirichlet
lemma transform_complex_moment_bound (T u v α : ℝ) (M : Nat)
    (hT : 0≤T+2*Real.pi*(20:ℝ)^2*v) (hα : 0≤α) (hα' : α<Real.pi/2) :
    ‖transform T 20 ((u:ℂ)+(v:ℂ)*I)‖ ≤
      boundConstant (T+2*Real.pi*(20:ℝ)^2*v) 20 α M*
        Real.exp (4*Real.pi*u*(1/4-(M:ℝ))+2*Real.pi^2*(20:ℝ)^2*v^2) := by
  rw [transform_complex_shift T 20 u v (by norm_num),norm_mul,Complex.norm_exp]
  have he : ((((2*Real.pi^2*(20:ℝ)^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*(20:ℝ)^2*u*v:ℝ):ℂ))).re=
      2*Real.pi^2*(20:ℝ)^2*v^2 := by
    simp only [sub_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero]
  rw [he]
  have hg := gamma_fourier_moment_bound (T+2*Real.pi*(20:ℝ)^2*v) 20 u α M hT
    (by norm_num) hα hα'
  apply (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans_eq
  unfold boundConstant
  simp only [Real.exp_add]
  ring
end RHBatch01GammaComplexFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01GammaCircle
open RHBatch01GammaFourier RHBatch01GammaComplexFourier RHBatch01FiniteDirichlet RHBatch01GammaTaylorFourier
lemma sphere_geometry (T x : ℝ) (hT : 20≤T) (z : ℂ) (hz : z∈sphere (x:ℂ) radius) :
    0≤T+2*Real.pi*(20:ℝ)^2*z.im ∧ x-radius≤z.re ∧
      2*Real.pi*(20:ℝ)^2*z.im≤20 ∧ 2*Real.pi^2*(20:ℝ)^2*z.im^2≤1/2 := by
  have hn : ‖z-(x:ℂ)‖=radius := mem_sphere_iff_norm.mp hz
  have hi : |z.im|≤radius := by simpa only [sub_im,ofReal_im,sub_zero,hn] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hr : |z.re-x|≤radius := by simpa only [sub_re,ofReal_re,hn] using Complex.abs_re_le_norm (z-(x:ℂ))
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (by positivity : 0≤800*Real.pi)
  have hu := mul_le_mul_of_nonneg_left (abs_le.mp hi).2 (by positivity : 0≤800*Real.pi)
  have hp : 800*Real.pi*radius=20 := by rw [mul_assoc,radius_pi];norm_num
  have hs : z.im^2≤radius^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) radius_pos.le).mpr hi
  have hv := mul_le_mul_of_nonneg_left hs (by positivity : 0≤800*Real.pi^2)
  rw [radius_quadratic] at hv
  constructor
  · nlinarith
  constructor
  · have := (abs_le.mp hr).1
    linarith
  constructor
  · nlinarith
  · nlinarith
lemma shifted_constant (T α v : ℝ) (M : Nat) :
    boundConstant (T+2*Real.pi*(20:ℝ)^2*v) 20 α M=
      boundConstant T 20 α M*Real.exp ((Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*v)) := by
  unfold boundConstant
  have he : Real.pi*(T+2*Real.pi*(20:ℝ)^2*v)/4-(T+2*Real.pi*(20:ℝ)^2*v)*α/2+
      (20:ℝ)^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/(20:ℝ)^2=
      (Real.pi*T/4-T*α/2+(20:ℝ)^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/(20:ℝ)^2)+
        (Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*v) := by ring
  rw [he,Real.exp_add,mul_assoc]
  ring
end RHBatch01GammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01GammaCircle
open RHBatch01GammaFourier RHBatch01GammaComplexFourier RHBatch01FiniteDirichlet RHBatch01GammaTaylorFourier
lemma transform_positive_sphere_bound (T x α : ℝ) (M : Nat) (hT : 20≤T)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) :
    ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖ ≤
      boundConstant T 20 α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ))+
        5*Real.pi+1/2+((M:ℝ)-1/4)/10) := by
  intro z hz
  have geom := sphere_geometry T x hT z hz
  have hg := transform_complex_moment_bound T z.re z.im α M geom.1 hα hα'
  rw [Complex.re_add_im,shifted_constant] at hg
  have hc0 : 0≤Real.pi/4-α/2 := by linarith
  have hc1 : Real.pi/4-α/2≤Real.pi/4 := by linarith
  have hm : (Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*z.im)≤5*Real.pi := by
    have he := mul_le_mul_of_nonneg_left geom.2.2.1 hc0
    nlinarith
  have hMr : (1:ℝ)≤M := by exact_mod_cast hM
  have hβ : 4*Real.pi*(1/4-(M:ℝ))≤0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hr := mul_le_mul_of_nonpos_left geom.2.1 hβ
  have he : (4*Real.pi*(1/4-(M:ℝ)))*radius= -((M:ℝ)-1/4)/10 := by
    unfold radius
    field_simp [Real.pi_ne_zero]
    ring
  have hu : 4*Real.pi*z.re*(1/4-(M:ℝ))≤4*Real.pi*x*(1/4-(M:ℝ))+((M:ℝ)-1/4)/10 := by
    nlinarith
  have hB : 0≤boundConstant T 20 α M := by
    have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
    unfold boundConstant
    positivity
  calc
    _ ≤ _ := hg
    _ = boundConstant T 20 α M*Real.exp ((Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*z.im)+
      4*Real.pi*z.re*(1/4-(M:ℝ))+2*Real.pi^2*(20:ℝ)^2*z.im^2) := by
      rw [mul_assoc,←Real.exp_add];congr 2;ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      nlinarith [geom.2.2.2]
end RHBatch01GammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHBatch01ScaledMomentFourier
open RHBatch01GammaCircle RHBatch01GammaComplexFourier RHBatch01GammaTaylorFourier RHBatch01GammaTimeTail RHBatch01FiniteDirichlet
lemma fourier_scaled (T x : ℝ) (k : Nat) :
    𝓕 (scaledMoment T k) x=𝓕 (moment T k) x/((k.factorial:ℂ)*(512:ℂ)^k) := by
  simp only [Real.fourier_real_eq_integral_exp_smul,scaledMoment,smul_eq_mul,div_eq_mul_inv,mul_assoc]
  simp only [←mul_assoc]
  rw [integral_mul_const]
lemma norm_fourier_scaled (T x : ℝ) (k : Nat) :
    ‖𝓕 (scaledMoment T k) x‖=‖𝓕 (moment T k) x‖/((k.factorial:ℝ)*(512:ℝ)^k) := by
  rw [fourier_scaled,norm_div,norm_mul,norm_natCast,norm_pow,norm_ofNat]
lemma scaled_cauchy_bound (T x C : ℝ) (k : Nat) (hC : 0≤C)
    (hB : ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖≤C) :
    ‖𝓕 (scaledMoment T k) x‖≤C*(5/16:ℝ)^k := by
  rw [norm_fourier_scaled]
  have hc := moment_fourier_cauchy T x radius C k radius_pos hB
  have hb := div_le_div_of_nonneg_right hc (show 0≤(512:ℝ)^k by positivity)
  have he : (C/radius^k)/(512:ℝ)^k=C*(40*Real.pi/512)^k := by
    unfold radius
    rw [div_pow]
    field_simp [Real.pi_ne_zero]
    rw [div_pow,one_pow]
    field_simp
  rw [←div_mul_eq_div_div,he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Real.pi_lt_four]
lemma scaled_negative_bound (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (scaledMoment T k) x‖≤12*Real.pi*Real.exp (Real.pi*x)*(5/16:ℝ)^k := by
  rw [norm_fourier_scaled]
  exact moment_negative_bound T x k hT
lemma scaled_positive_bound (T x α : ℝ) (M k : Nat) (hT : 20≤T)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) :
    ‖𝓕 (scaledMoment T k) x‖≤
      (boundConstant T 20 α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ))+
        5*Real.pi+1/2+((M:ℝ)-1/4)/10))*(5/16:ℝ)^k := by
  apply scaled_cauchy_bound
  · have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
    unfold boundConstant
    positivity
  · exact transform_positive_sphere_bound T x α M hT hα hα' hM
end RHBatch01ScaledMomentFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01ScaledMomentFourier
open RHBatch01FiniteDirichlet RHBatch01GammaTimeTail
noncomputable def positiveConstant (T : ℝ) : ℝ := boundConstant T 20 0 1*Real.exp (5*Real.pi+23/40)
noncomputable def decayConstant (T : ℝ) : ℝ := 12*Real.pi+positiveConstant T
lemma positive_constant_nonneg (T : ℝ) : 0≤positiveConstant T := by
  unfold positiveConstant boundConstant
  norm_num
  positivity
lemma positive_envelope (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (scaledMoment T k) x‖≤positiveConstant T*Real.exp (-3*Real.pi*x) := by
  have hp := scaled_positive_bound T x 0 1 k hT (by norm_num) (by positivity) (by norm_num)
  simp only [Nat.cast_one] at hp
  have he : 4*Real.pi*x*(1/4-(1:ℝ))+5*Real.pi+1/2+((1:ℝ)-1/4)/10=
      -3*Real.pi*x+(5*Real.pi+23/40) := by ring
  rw [he,Real.exp_add] at hp
  have hpow : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ (boundConstant T 20 0 1*(Real.exp (-3*Real.pi*x)*Real.exp (5*Real.pi+23/40)))*(5/16:ℝ)^k := hp
    _ = (positiveConstant T*Real.exp (-3*Real.pi*x))*(5/16:ℝ)^k := by unfold positiveConstant;ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (positive_constant_nonneg T) (Real.exp_pos (-3*Real.pi*x)).le)
      simpa only [mul_one] using hm
lemma fourier_decay (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (scaledMoment T k) x‖≤decayConstant T*Real.exp (-Real.pi*|x|) := by
  have hC := positive_constant_nonneg T
  have hpC : 12*Real.pi≤decayConstant T := by unfold decayConstant;linarith
  have hpC' : positiveConstant T≤decayConstant T := by unfold decayConstant;linarith [Real.pi_pos]
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
    apply (positive_envelope T x k hT).trans
    apply mul_le_mul hpC' _ (Real.exp_pos _).le (by unfold decayConstant;positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  · have hx' : x≤0 := (le_of_not_ge hx)
    rw [abs_of_nonpos hx']
    have he : -Real.pi*(-x)=Real.pi*x := by ring
    rw [he]
    have hg := scaled_negative_bound T x k hT
    have hpow : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      _ ≤ (12*Real.pi*Real.exp (Real.pi*x))*(5/16:ℝ)^k := hg
      _ ≤ 12*Real.pi*Real.exp (Real.pi*x) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0≤12*Real.pi*Real.exp (Real.pi*x) by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpC (Real.exp_pos _).le
end RHBatch01ScaledMomentFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01ScaledMomentFourier
open RHBatch01GammaTimeTail
lemma summable_exp_abs_int (c : ℝ) (hc : 0<c) :
    Summable (fun n : Int => Real.exp (-c*|(n:ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have ht := Real.summable_exp_nat_mul_iff.mpr (by linarith : -c<0)
  have hp : (fun n : Nat => Real.exp (-c*|((n:Int):ℝ)|))=(fun n : Nat => Real.exp ((n:ℝ)*(-c))) := by
    ext n
    simp only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ)≤n from Nat.cast_nonneg n)]
    congr 1
    ring
  have hn : (fun n : Nat => Real.exp (-c*|((-n:Int):ℝ)|))=(fun n : Nat => Real.exp ((n:ℝ)*(-c))) := by
    ext n
    simp only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (show (0:ℝ)≤n from Nat.cast_nonneg n)]
    congr 1
    ring
  rw [hp,hn]
  exact ⟨ht,ht⟩
lemma moment_fourier_norm_summable (T B : ℝ) (k : Nat) (hT : 20≤T) (hB : 0<B) :
    Summable (fun n : Int => ‖𝓕 (scaledMoment T k) ((n:ℝ)/B)‖) := by
  have hg := (summable_exp_abs_int (Real.pi/B) (by positivity)).mul_left (decayConstant T)
  apply hg.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  have hb := fourier_decay T ((n:ℝ)/B) k hT
  rw [abs_div,abs_of_pos hB] at hb
  have he : -Real.pi*(|(n:ℝ)|/B)= -(Real.pi/B)*|(n:ℝ)| := by ring
  simpa only [he] using hb
end RHBatch01ScaledMomentFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter Asymptotics
open scoped FourierTransform Topology
namespace RHBatch01GammaSampling
open RHBatch01GammaTimeTail RHBatch01ScaledMomentFourier RHBatch01Fourier
lemma rescaled_moment_decay (T B : ℝ) (k : Nat) (hB : 0<B) :
    (fun t : ℝ => scaledMoment T k (B*t))=O[cocompact ℝ] (fun t : ℝ => |t|^(-(2:ℝ))) := by
  let g : ℝ→ℂ := fun t => Complex.exp (-((B^2/1600:ℝ):ℂ)*(t:ℂ)^2)
  have he (t : ℝ) : ‖g t‖=Real.exp (-(B*t)^2/1600) := by
    dsimp [g]
    rw [norm_cexp_neg_mul_sq,Complex.ofReal_re]
    congr 1
    ring
  have hg : (fun t : ℝ => scaledMoment T k (B*t))=O[cocompact ℝ] g := by
    apply isBigO_iff.mpr
    refine ⟨18,Eventually.of_forall (fun t => ?_)⟩
    rw [he]
    exact scaled_moment_gaussian T (B*t) k
  have ha : 0<(((B^2/1600:ℝ):ℂ)).re := by
    have hp : 0<(B^2/1600:ℝ) := div_pos (sq_pos_of_pos hB) (by norm_num)
    simpa only [Complex.ofReal_re] using hp
  have hl := (isLittleO_exp_neg_mul_sq_cocompact (a:=((B^2/1600:ℝ):ℂ)) ha (-(2:ℝ))).isBigO
  exact hg.trans hl
lemma rescaled_moment_fourier_summable (T B : ℝ) (k : Nat) (hT : 20≤T) (hB : 0<B) :
    Summable (fun n : Int => 𝓕 (fun t : ℝ => scaledMoment T k (B*t)) (n:ℝ)) := by
  simp_rw [fourier_scale (scaledMoment T k) B hB]
  exact ((moment_fourier_norm_summable T B k hT hB).of_norm).mul_left _
lemma gamma_moment_poisson (T B x : ℝ) (k : Nat) (hT : 20≤T) (hB : 0<B) :
    (∑' q : Int, scaledMoment T k (x+(q:ℝ)*B))=
      (B⁻¹:ℂ)*∑' q : Int, 𝓕 (scaledMoment T k) ((q:ℝ)/B)*RHBatch01Fourier.phase ((q:ℝ)*x/B) := by
  let g : ℝ→ℂ := fun t => scaledMoment T k (B*t)
  have hc : Continuous g := (scaled_moment_continuous T k).comp (by fun_prop)
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (by norm_num : (1:ℝ)<2)
    (rescaled_moment_decay T B k hB) (rescaled_moment_fourier_summable T B k hT hB) (x/B)
  have hl (q : Int) : g (x/B+(q:ℝ))=scaledMoment T k (x+(q:ℝ)*B) := by
    dsimp [g]
    congr 1
    field_simp [hB.ne'] <;> ring
  have hr (q : Int) : 𝓕 g (q:ℝ)=(B⁻¹:ℂ)*𝓕 (scaledMoment T k) ((q:ℝ)/B) :=
    fourier_scale (scaledMoment T k) B hB (q:ℝ)
  have hp (q : Int) : fourier q ((x/B:ℝ):UnitAddCircle)=RHBatch01Fourier.phase ((q:ℝ)*x/B) := by
    rw [fourier_coe_apply]
    unfold RHBatch01Fourier.phase
    congr 1
    push_cast
    ring
  simp_rw [hl,hr,hp,mul_assoc] at h
  rw [tsum_mul_left] at h
  exact h
end RHBatch01GammaSampling
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHBatch01GammaSampling
open RHBatch01GammaTimeTail RHBatch01ScaledMomentFourier RHBatch01Fourier
lemma gamma_poisson_dft_pair {N : Nat} [NeZero N] (T B : ℝ) (k : Nat)
    (hT : 20≤T) (hB : 0<B) (n : Int) :
    (∑' q : Int, scaledMoment T k ((n:ℝ)*B/(N:ℝ)+(q:ℝ)*B))=
      (B⁻¹:ℂ)*∑ m : Fin N,
        (∑' q : Int, 𝓕 (scaledMoment T k) (((q*(N:Int)+(m.val:Int)):ℝ)/B))*
          RHBatch01Fourier.phase ((m.val:ℝ)*(n:ℝ)/(N:ℝ)) := by
  rw [gamma_moment_poisson T B _ k hT hB]
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  have hc (j : Int) : (j:ℝ)*((n:ℝ)*B/(N:ℝ))/B=(j:ℝ)*(n:ℝ)/(N:ℝ) := by field_simp <;> ring
  simp_rw [hc]
  let H : Int→ℂ := fun j => 𝓕 (scaledMoment T k) ((j:ℝ)/B)*RHBatch01Fourier.phase ((j:ℝ)*(n:ℝ)/(N:ℝ))
  have hH : Summable H := by
    apply Summable.of_norm_bounded (moment_fourier_norm_summable T B k hT hB)
    intro j
    simp only [H,norm_mul,RHBatch01Fourier.phase_norm,mul_one,le_refl]
  rw [split_integer_tsum (N:=N) H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hp (q : Int) : RHBatch01Fourier.phase ((((q*(N:Int)+(m.val:Int)):Int):ℝ)*(n:ℝ)/(N:ℝ))=
      RHBatch01Fourier.phase ((m.val:ℝ)*(n:ℝ)/(N:ℝ)) := by
    have he : (((q*(N:Int)+(m.val:Int)):Int):ℝ)*(n:ℝ)/(N:ℝ)=
        (m.val:ℝ)*(n:ℝ)/(N:ℝ)+((q*n:Int):ℝ) := by push_cast;field_simp;ring
    rw [he,RHBatch01Fourier.phase_add_int]
  simp only [H]
  simp_rw [hp]
  rw [tsum_mul_right]
  congr 1
  apply tsum_congr
  intro q
  push_cast
  rfl
end RHBatch01GammaSampling
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHBatch01GammaTimeTail
lemma geometric_error_hasSum : HasSum (fun n : Nat => 6*Real.exp (-64*(n+1:ℝ)))
    (6*Real.exp (-64)/(1-Real.exp (-64))) := by
  have hq0 : 0≤Real.exp (-64) := (Real.exp_pos _).le
  have hq1 : Real.exp (-64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (6*Real.exp (-64))
  have hefun : (fun n : Nat => 6*Real.exp (-64*(n+1:ℝ)))=
      (fun n : Nat => (6*Real.exp (-64))*Real.exp (-64)^n) := by
    ext n
    have he : -64*(n+1:ℝ)=(-64:ℝ)+(n:ℝ)*(-64) := by ring
    rw [he,Real.exp_add,Real.exp_nat_mul]
    ring
  rw [hefun,show 6*Real.exp (-64)/(1-Real.exp (-64))=
    6*Real.exp (-64)*(1-Real.exp (-64))⁻¹ by ring]
  exact h
lemma geometric_error_small : 12*Real.exp (-64)/(1-Real.exp (-64))≤1/10^18 := by
  have hq1 : Real.exp (-64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hp : (2:ℝ)^64≤Real.exp 64 := by
    have he : Real.exp (64:ℝ)=(Real.exp 1)^64 := by simpa using Real.exp_nat_mul (1:ℝ) (64:Nat)
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_two]) _
  have he : Real.exp (-64)*Real.exp 64=1 := by rw [←Real.exp_add];norm_num
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-64)).le
  rw [he] at hm
  have hq : Real.exp (-64)≤1/(2:ℝ)^64 := (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hm)
  calc
    _ ≤ 12/((2:ℝ)^64-1) := by
      apply (div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ)<2^64-1)).mpr
      norm_num at hq ⊢
      nlinarith
    _ ≤ _ := by norm_num
lemma time_alias_mass (T t : ℝ) (k : Nat) (ht : -256≤t ∧ t≤256) :
    (∑' n : Nat, ‖scaledMoment T k (t+(n+1:ℝ)*512)‖)+
      (∑' n : Nat, ‖scaledMoment T k (t-(n+1:ℝ)*512)‖)≤1/10^18 := by
  have hg := geometric_error_hasSum.summable
  have hp := hg.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => positive_alias_term T t k n ht.1)
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => negative_alias_term T t k n ht.2)
  have hpb := hp.tsum_le_tsum (fun n => positive_alias_term T t k n ht.1) hg
  have hnb := hn.tsum_le_tsum (fun n => negative_alias_term T t k n ht.2) hg
  rw [geometric_error_hasSum.tsum_eq] at hpb hnb
  calc
    _ ≤ (6*Real.exp (-64)/(1-Real.exp (-64)))+
        (6*Real.exp (-64)/(1-Real.exp (-64))) := add_le_add hpb hnb
    _ = 12*Real.exp (-64)/(1-Real.exp (-64)) := by ring
    _ ≤ _ := geometric_error_small
end RHBatch01GammaTimeTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform
namespace RHBatch01GammaFixedBounds
open RHBatch01GammaTimeTail RHBatch01ScaledMomentFourier RHBatch01FiniteDirichlet
noncomputable def angle (T : ℝ) : ℝ := Real.pi/2-1/T
lemma angle_admissible (T : ℝ) (hT : 3000000000≤T) :
    0≤angle T ∧ angle T<Real.pi/2 := by
  have ht : 0<T := by linarith
  have hi : 1/T≤1 := (div_le_one ht).mpr (by linarith)
  unfold angle
  constructor <;> linarith [Real.pi_gt_three,div_pos (by norm_num : (0:ℝ)<1) ht]
lemma fixed_constant (T : ℝ) (hT : 3000000000≤T ∧ T≤4000000000) :
    boundConstant T 20 (angle T) 122≤Real.exp 10000 := by
  have ht : 0<T := by linarith
  have hlo : (1:ℝ)/4000000000≤1/T := div_le_div_of_nonneg_left (by norm_num) ht hT.2
  have hhi : (1:ℝ)/T≤1/100 := (div_le_div_iff₀ ht (by norm_num)).mpr (by linarith)
  have hc : (1:ℝ)/2^33≤Real.cos (angle T) := by
    rw [angle,Real.cos_pi_div_two_sub]
    have hs := RHBatch01MomentEnvelope.sin_small_lower (1/T) (by positivity) hhi
    linarith
  have hcp : 0<Real.cos (angle T) := lt_of_lt_of_le (by positivity) hc
  have hf : 4*Real.pi*((122).factorial:ℝ)/(Real.cos (angle T))^122≤(2:ℝ)^5000 := by
    calc
      _ ≤ 16*((122).factorial:ℝ)/((1:ℝ)/2^33)^122 := by
        apply div_le_div₀
        · positivity
        · nlinarith [Real.pi_lt_four]
        · positivity
        · exact pow_le_pow_left₀ (by positivity) hc _
      _ = ((16*(122).factorial*2^(33*122):Nat):ℝ) := by
        push_cast
        rw [div_pow,one_pow,one_div,div_inv_eq_mul,←pow_mul]
      _ ≤ _ := by
        exact_mod_cast (show 16*(122).factorial*2^(33*122)≤2^5000 from by decide +kernel)
  have heq : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(122:ℝ))^2/(20:ℝ)^2=1/2+50/T^2+237169/3200 := by
    unfold angle
    field_simp
    ring
  have hs : 50/T^2≤1/2 := (div_le_div_iff₀ (sq_pos_of_pos ht) (by norm_num)).mpr (by nlinarith)
  have he : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(122:ℝ))^2/(20:ℝ)^2≤80 := by rw [heq];linarith
  have hp : (2:ℝ)^5000≤Real.exp 5000 := by
    rw [show Real.exp (5000:ℝ)=(Real.exp 1)^5000 by simpa using Real.exp_nat_mul (1:ℝ) (5000:Nat)]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  unfold boundConstant
  calc
    _ ≤ (2:ℝ)^5000*Real.exp 80 := mul_le_mul hf (Real.exp_le_exp.mpr he) (by positivity) (by positivity)
    _ ≤ Real.exp 5000*Real.exp 80 := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = Real.exp 5080 := by rw [←Real.exp_add];norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
lemma positive_frequency_alias_term (T x : ℝ) (k n : Nat)
    (hT : 3000000000≤T ∧ T≤4000000000) (hx : 0≤x) :
    ‖𝓕 (scaledMoment T k) (x+32*(n+1:ℝ))‖≤Real.exp (-128*(n+1:ℝ)) := by
  have ha := angle_admissible T hT.1
  have hb := scaled_positive_bound T (x+32*(n+1:ℝ)) (angle T) 122 k
    (by linarith) ha.1 ha.2 (by norm_num)
  have hk : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have he : 10000+(4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
      5*Real.pi+1/2+((122:ℝ)-1/4)/10)≤-128*(n+1:ℝ) := by
    have hxp : (0:ℝ)≤Real.pi*x := mul_nonneg Real.pi_pos.le hx
    have hnp : 3*(n+1:ℝ)≤Real.pi*(n+1:ℝ) := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
    nlinarith [Real.pi_lt_four]
  calc
    _ ≤ (boundConstant T 20 (angle T) 122*Real.exp (4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10))*(5/16:ℝ)^k := hb
    _ ≤ Real.exp 10000*Real.exp (4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10) := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (fixed_constant T hT) (by positivity)) (by positivity)).trans
      exact mul_le_of_le_one_right (by positivity) hk
    _ = Real.exp (10000+(4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr he
lemma negative_frequency_alias_term (T x : ℝ) (k n : Nat) (hT : 20≤T) (hx : x≤5) :
    ‖𝓕 (scaledMoment T k) (x-32*(n+1:ℝ))‖≤48*Real.exp (-81*(n+1:ℝ)) := by
  have hb := scaled_negative_bound T (x-32*(n+1:ℝ)) k hT
  have hk : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hs : x-32*(n+1:ℝ)≤0 := by linarith
  have he : Real.pi*(x-32*(n+1:ℝ))≤-81*(n+1:ℝ) := by
    have hp := mul_le_mul_of_nonpos_right Real.pi_gt_three.le hs
    nlinarith
  calc
    _ ≤ 12*Real.pi*Real.exp (Real.pi*(x-32*(n+1:ℝ)))*(5/16:ℝ)^k := hb
    _ ≤ 12*Real.pi*Real.exp (Real.pi*(x-32*(n+1:ℝ))) := mul_le_of_le_one_right (by positivity) hk
    _ ≤ _ := mul_le_mul (by linarith [Real.pi_lt_four]) (Real.exp_le_exp.mpr he) (by positivity) (by norm_num)
end RHBatch01GammaFixedBounds
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHBatch01ExponentialGeometric
lemma tail_hasSum (A c : ℝ) (hc : 0 < c) :
    HasSum (fun n : Nat => A*Real.exp (-c*(n+1:ℝ)))
      (A*Real.exp (-c)/(1-Real.exp (-c))) := by
  have h := (hasSum_geometric_of_lt_one (Real.exp_pos (-c)).le
    (Real.exp_lt_one_iff.mpr (by linarith))).mul_left (A*Real.exp (-c))
  have hf : (fun n : Nat => A*Real.exp (-c*(n+1:ℝ)))=
      (fun n : Nat => (A*Real.exp (-c))*Real.exp (-c)^n) := by
    ext n
    rw [show -c*(n+1:ℝ)= -c+(n:ℝ)*(-c) by ring,Real.exp_add,Real.exp_nat_mul]
    ring
  rw [hf]
  convert h using 1 <;> first | rfl | ring
lemma tail_bound (A b : ℝ) (c : Nat) (hA : 0≤A) (hb : 1 < b) (hc : 0 < c)
    (he : b≤Real.exp 1) :
    (∑' n : Nat, A*Real.exp (-(c:ℝ)*(n+1:ℝ)))≤A/(b^c-1) := by
  have hcr : (0:ℝ)<c := by exact_mod_cast hc
  rw [(tail_hasSum A c hcr).tsum_eq]
  have hp : b^c≤Real.exp (c:ℝ) := by
    rw [show Real.exp (c:ℝ)=(Real.exp 1)^c by simpa using Real.exp_nat_mul (1:ℝ) c]
    exact pow_le_pow_left₀ (by linarith) he _
  have hbpow : 1 < b^c := one_lt_pow₀ hb hc.ne'
  have hd : 0<Real.exp (c:ℝ)-1 := by linarith
  have hq : 1-Real.exp (-(c:ℝ))≠0 := by
    have hq' : Real.exp (-(c:ℝ))<1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hi : A*Real.exp (-(c:ℝ))/(1-Real.exp (-(c:ℝ)))=A/(Real.exp (c:ℝ)-1) := by
    rw [Real.exp_neg]
    field_simp
  rw [hi]
  exact div_le_div_of_nonneg_left hA (by linarith) (by linarith)
end RHBatch01ExponentialGeometric
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform
namespace RHBatch01GammaFixedBounds
open RHBatch01GammaTimeTail RHBatch01ExponentialGeometric
lemma frequency_alias_mass (T x : ℝ) (k : Nat)
    (hT : 3000000000≤T ∧ T≤4000000000) (hx : 0≤x ∧ x≤5) :
    (∑' n : Nat, ‖𝓕 (scaledMoment T k) (x+32*(n+1:ℝ))‖)+
      (∑' n : Nat, ‖𝓕 (scaledMoment T k) (x-32*(n+1:ℝ))‖)≤2/10^31 := by
  have hsp := (tail_hasSum 1 128 (by norm_num)).summable
  have hsn := (tail_hasSum 48 81 (by norm_num)).summable
  have hp := hsp.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by simpa only [one_mul] using positive_frequency_alias_term T x k n hT hx.1)
  have hn := hsn.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => negative_frequency_alias_term T x k n (by linarith [hT.1]) hx.2)
  have hpb := hp.tsum_le_tsum
    (fun n => by simpa only [one_mul] using positive_frequency_alias_term T x k n hT hx.1) hsp
  have hnb := hn.tsum_le_tsum
    (fun n => negative_frequency_alias_term T x k n (by linarith [hT.1]) hx.2) hsn
  have hpe := tail_bound 1 2 128 (by norm_num) (by norm_num) (by norm_num) Real.exp_one_gt_two.le
  have hne := tail_bound 48 (8/3) 81 (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.exp_one_gt_d9])
  calc
    _ ≤ (1/((2:ℝ)^128-1))+(48/((8/3:ℝ)^81-1)) :=
      add_le_add (hpb.trans hpe) (hnb.trans hne)
    _ ≤ _ := by norm_num
end RHBatch01GammaFixedBounds
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHBatch01IntegerTsum
lemma error (f : Int→ℂ)
    (hp : Summable (fun n : Nat => ‖f (n+1)‖))
    (hn : Summable (fun n : Nat => ‖f (-(n+1))‖)) :
    ‖(∑' n : Int, f n)-f 0‖≤
      (∑' n : Nat, ‖f (n+1)‖)+(∑' n : Nat, ‖f (-(n+1))‖) := by
  rw [tsum_of_add_one_of_neg_add_one hp.of_norm hn.of_norm]
  have he : (∑' n : Nat, f (n+1))+f 0+(∑' n : Nat, f (-(n+1)))-f 0=
      (∑' n : Nat, f (n+1))+(∑' n : Nat, f (-(n+1))) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_tsum_le_tsum_norm hp) (norm_tsum_le_tsum_norm hn))
end RHBatch01IntegerTsum
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex MeasureTheory Finset
open scoped FourierTransform
namespace RHBatch01GammaPoissonBridge
open RHBatch01GammaTimeTail RHBatch01GammaSampling RHBatch01ScaledMomentFourier
noncomputable def periodic (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  ∑' q:Int,scaledMoment T k (t+(q:ℝ)*512)
noncomputable def aliases (T : ℝ) (k : Nat) (m : Fin 16384) : ℂ :=
  ∑' q:Int,𝓕 (scaledMoment T k) (((q*(16384:Int)+(m.val:Int):Int):ℝ)/512)
lemma time_error (T : ℝ) (k : Nat) (t : ℝ) (ht:-256≤t ∧ t≤256) :
    ‖periodic T k t-scaledMoment T k t‖≤1/10^18 := by
  have hg:=geometric_error_hasSum.summable
  have hp:=hg.of_nonneg_of_le (fun n=>norm_nonneg _)
    (fun n=>positive_alias_term T t k n ht.1)
  have hn:=hg.of_nonneg_of_le (fun n=>norm_nonneg _)
    (fun n=>negative_alias_term T t k n ht.2)
  let f:Int→ℂ:=fun q=>scaledMoment T k (t+(q:ℝ)*512)
  have hp':Summable (fun n:Nat=>‖f ((n:Int)+1)‖) := by
    dsimp only [f]
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hp
  have hn':Summable (fun n:Nat=>‖f (-((n:Int)+1))‖) := by
    dsimp only [f]
    simpa only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,neg_mul,sub_eq_add_neg] using hn
  have h:=RHBatch01IntegerTsum.error f hp' hn'
  dsimp only [f] at h
  simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,neg_mul,←sub_eq_add_neg,
    Int.cast_zero,zero_mul,add_zero] at h
  exact h.trans (time_alias_mass T t k ht)

lemma frequency_error (T : ℝ) (hT : 3000000000≤T ∧ T≤4000000000) (k : Nat) (m : Fin 16384) (hm:m.val≤1953) :
    ‖𝓕 (scaledMoment T k) ((m.val:ℝ)/512)-aliases T k m‖≤2/10^31 := by
  let f:Int→ℂ:=fun q=>𝓕 (scaledMoment T k)
    (((q*(16384:Int)+(m.val:Int):Int):ℝ)/512)
  have hs:Summable (fun q:Int=>‖f q‖) :=
    (moment_fourier_norm_summable T 512 k (by linarith [hT.1]) (by norm_num)).comp_injective
      (show Function.Injective (fun q:Int=>q*16384+(m.val:Int)) from by intro a b h; dsimp at h; omega)
  have hp:=hs.comp_injective (show Function.Injective (fun n:Nat=>(n:Int)+1) from by intro a b h; dsimp at h; omega)
  have hn:=hs.comp_injective (show Function.Injective (fun n:Nat=>-((n:Int)+1)) from by intro a b h; dsimp at h; omega)
  have h:=RHBatch01IntegerTsum.error f hp hn
  have heP (n:Nat) : f ((n:Int)+1)=𝓕 (scaledMoment T k) ((m.val:ℝ)/512+32*(n+1:ℝ)) := by
    unfold f
    congr 1
    push_cast
    ring
  have heN (n:Nat) : f (-((n:Int)+1))=𝓕 (scaledMoment T k) ((m.val:ℝ)/512-32*(n+1:ℝ)) := by
    unfold f
    congr 1
    push_cast
    ring
  simp_rw [heP,heN] at h
  have hx:0≤(m.val:ℝ)/512 ∧ (m.val:ℝ)/512≤5 := by
    have hmR:(m.val:ℝ)≤1953:=by exact_mod_cast hm
    constructor
    · positivity
    · linarith
  have ht:=RHBatch01GammaFixedBounds.frequency_alias_mass T ((m.val:ℝ)/512) k hT hx
  have hh:=h.trans ht
  rw [norm_sub_rev] at hh
  simpa only [f,aliases,Int.cast_zero,zero_mul,zero_add,Int.cast_natCast] using hh
lemma sample_time (i : Nat) : RHHighSamplingFunctions.sampleTime i=
    (((i:Int)-8192: Int):ℝ)*512/16384 := by
  unfold RHHighSamplingFunctions.sampleTime RHHighSamplingFunctions.sampleIndex
  push_cast
  ring
lemma pair (T : ℝ) (hT : 20≤T) (k : Nat) (i : Fin 16384) :
    periodic T k (RHHighSamplingFunctions.sampleTime i.val)=
    ((512:ℝ)⁻¹:ℂ)*∑ m:Fin 16384,aliases T k m*
      RHBatch01Fourier.phase ((m.val:ℝ)*((i.val:ℝ)-8192)/16384) := by
  have h:=gamma_poisson_dft_pair (N:=16384) T 512 k hT (by norm_num) ((i.val:Int)-8192)
  rw [sample_time]
  dsimp only [periodic,aliases]
  push_cast at h ⊢
  exact h
lemma fourier_from_dft (T : ℝ) (hT : 3000000000≤T ∧ T≤4000000000) (k : Nat) (m : Fin 16384) (hm:m.val≤1953) (d : ℂ)
    (hd:‖RHBatch01ChirpDFT.dft (fun i:Fin 16384=>RHHighSamplingFunctions.moment T k
      (RHHighSamplingFunctions.sampleTime i.val)) m-d‖≤1/10^16) :
    ‖𝓕 (RHHighSamplingFunctions.moment T k) ((m.val:ℝ)/512)-
      RHBatch01Fourier.phase ((m.val:ℝ)/2)*((1/32:ℂ)*d)‖≤1/10^15 := by
  have hfun:(RHHighSamplingFunctions.moment T k:ℝ→ℂ)=scaledMoment T k := by
    funext t
    exact RHHighSamplingFunctions.moment_eq _ _ _
  have ht (i:Fin 16384):‖periodic T k (RHHighSamplingFunctions.sampleTime i.val)-
      RHHighSamplingFunctions.moment T k (RHHighSamplingFunctions.sampleTime i.val)‖≤1/10^18 := by
    rw [hfun]
    apply time_error T
    unfold RHHighSamplingFunctions.sampleTime RHHighSamplingFunctions.sampleIndex
    have hi:(0:ℝ) ≤ i.val ∧ (i.val:ℝ)≤16383 :=by constructor;positivity;exact_mod_cast (show i.val≤16383 by omega)
    push_cast
    constructor <;> linarith
  have hf:=frequency_error T hT k m hm
  rw [←hfun] at hf
  exact RHBatch01GammaDiscreteBudget.fourier_fixed
    (fun i=>periodic T k (RHHighSamplingFunctions.sampleTime i.val))
    (fun i=>RHHighSamplingFunctions.moment T k (RHHighSamplingFunctions.sampleTime i.val))
    (aliases T k) d m (pair T (by linarith [hT.1]) k) ht hd _ hf
end RHBatch01GammaPoissonBridge
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
open scoped ComplexConjugate FourierTransform
namespace RHBatch01GammaDFTBridge
open RHBatch01PackedFFTSound
lemma chirp_value (j : Nat) :
    pairValue (RHHighFFTArithmeticBase.chirp j)=RHBatch01IndexedChirpAccuracy.value j := rfl
lemma conjugate_error (j : Nat) (hj:j<32767) :
    ‖RHBatch01ChirpDFT.phase (-(j:ℝ)^2/16384)-
      conj (pairValue (RHHighFFTArithmeticBase.chirp j))‖≤1/10^23 := by
  rw [chirp_value,show -(j:ℝ)^2/16384= -((j:ℝ)^2/16384) by ring,
    ←RHBatch01IndexedChirpAccuracy.phase_conj,←map_sub,Complex.norm_conj,norm_sub_rev]
  exact RHBatch01IndexedChirpAccuracy.enclosure j hj
lemma kernel_error (n j : Fin 16384) :
    ‖RHBatch01ChirpDFT.phase (((n.val:ℝ)-(j.val:ℝ))^2/16384)-
      pairValue (RHHighFFTArithmeticBase.chirp ((n.val:Int)-(j.val:Int)).natAbs)‖≤1/10^23 := by
  have hsq:((((n.val:Int)-(j.val:Int)).natAbs:ℝ))^2=((n.val:ℝ)-(j.val:ℝ))^2 := by
    rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,sq_abs]
  rw [chirp_value,←hsq,norm_sub_rev]
  apply RHBatch01IndexedChirpAccuracy.enclosure
  have hn:=n.isLt
  have hj:=j.isLt
  omega
lemma fourier_from_arrays (T : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (k : Nat) (hk:k<26)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hsample:∀ i:Fin 16384,
      ‖RHHighSamplingFunctions.moment (T:ℝ) k (RHHighSamplingFunctions.sampleTime i.val)-
        RHBatch01RawChirpedInput.value (RHFastKernelMomentArithmetic.moment i.val
          (RHFastKernelGammaArithmetic.compute T i.val) k)‖≤1/10^23)
    (hinput:∀ j:Fin 16384,
      RHBatch01RawChirpedInput.product (RHFastKernelMomentArithmetic.moment j.val
        (RHFastKernelGammaArithmetic.compute T j.val) k) (RHHighFFTArithmeticBase.chirp j.val)=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (m : Fin 2048) (hm:m.val≤1953) :
    ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) ((m.val:ℝ)/512)-
      RHBatch01Fourier.phase ((m.val:ℝ)/2)*((1/32:ℂ)*
        pairValue (((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[m.val]?).getD (0,0)))‖≤1/10^15 := by
  let a:Fin 16384→ℂ:=fun j=>RHHighSamplingFunctions.moment (T:ℝ) k (RHHighSamplingFunctions.sampleTime j.val)
  let ap:Fin 16384→ℂ:=fun j=>RHBatch01RawChirpedInput.value (RHFastKernelMomentArithmetic.moment j.val (RHFastKernelGammaArithmetic.compute T j.val) k)
  let b:Fin 16384→ℂ:=fun j=>RHBatch01ChirpDFT.phase (-(j.val:ℝ)^2/16384)
  let bp:Fin 16384→ℂ:=fun j=>conj (pairValue (RHHighFFTArithmeticBase.chirp j.val))
  let c:Fin 16384→Fin 16384→ℂ:=fun n j=>RHBatch01ChirpDFT.phase (((n.val:ℝ)-(j.val:ℝ))^2/16384)
  let cp:Fin 16384→Fin 16384→ℂ:=fun n j=>pairValue (RHHighFFTArithmeticBase.chirp ((n.val:Int)-(j.val:Int)).natAbs)
  have hi (j:Fin 16384):
      (((((ar j:Int)-2^166:Int):ℂ)+(((ai j:Int)-2^166:Int):ℂ)*I)/(2:ℂ)^160)=ap j*bp j := by
    have hh:=congrArg (fun p:Int×Int=>((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^160) (hinput j)
    rw [←hh]
    exact RHBatch01RawChirpedInput.product_value _ _
  have hc (j:Fin 16384):
      (((((br ⟨16383+m.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)+
        (((bi ⟨16383+m.val-j.val,by omega⟩:Int)-2^81:Int):ℂ)*I)/(2:ℂ)^80)=cp ⟨m.val,by omega⟩ j := by
    have h:=hkernel ⟨16383+m.val-j.val,by omega⟩
    have he:((16383+m.val-j.val:Nat):Int)-16383=(m.val:Int)-(j.val:Int):=by omega
    have hp:=congrArg pairValue h
    simpa only [pairValue,Prod.fst,Prod.snd,he,cp] using hp
  have hd:=analytic_error ar ai br bi RHHighFFTArithmeticBase.chirp m a ap b bp c cp
    (fun j=>RHHighSamplingFunctions.moment_norm _ _ _) (by intro j;rfl) (by intro n j;rfl)
    hsample (fun j=>conjugate_error j.val (by omega)) kernel_error hi hc (by rfl)
  have hf:=RHBatch01GammaPoissonBridge.fourier_from_dft (T:ℝ) (by constructor <;> norm_cast <;> omega) k ⟨m.val,by omega⟩ hm _ hd
  rw [output_vector ar ai br bi hAr hAi hBr hBi]
  simpa only [List.getElem?_ofFn,m.isLt,dif_pos,Option.getD_some,roundPair] using hf
end RHBatch01GammaDFTBridge
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Complex
namespace RHHighSamplingFunctions
open _root_.RHHighSamplingFunctions
lemma gamma_sample_eq (T i : Nat) (hT : 257≤T) (hi:i<16384) :
    gammaWindow (T:ℝ) (sampleTime i)=
      Complex.Gamma (1/4+((((T:Int)*32+sampleIndex i).toNat:ℂ)/64)*I)*
        Complex.exp (((Real.pi*((((T:Int)*32+sampleIndex i).toNat:ℝ)/64)/2-
          ((sampleIndex i:ℝ)/32)^2/800:ℝ):ℂ)) := by
  have hn:(0:Int)≤(T:Int)*32+sampleIndex i := by unfold sampleIndex;omega
  have hb:((((T:Int)*32+sampleIndex i).toNat:ℝ)/64)=(sampleTime i+(T:ℝ))/2 := by
    have h:=congrArg (fun a:Int=>(a:ℝ)) (Int.toNat_of_nonneg hn)
    push_cast at h
    unfold sampleTime
    linarith
  have hc:(((T:Int)*32+sampleIndex i).toNat:ℂ)/64=(((sampleTime i+(T:ℝ))/2:ℝ):ℂ) := by
    have h:=congrArg Complex.ofReal hb
    push_cast at h ⊢
    exact h
  unfold gammaWindow
  rw [hb,hc]
  congr 2
  unfold sampleTime
  push_cast
  ring
lemma moment_enclosure (T i k : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (hi:i<16384) (hk:k<26) :
    ‖moment (T:ℝ) k (sampleTime i)-
      RHBatch01RawChirpedInput.value (RHFastKernelMomentArithmetic.moment i (RHFastKernelGammaArithmetic.compute T i) k)‖≤1/10^23 := by
  have h:=TaoFivePrimes.rh_fast_kernel_moment_uniform_analytic T i k hT hU hi hk
  unfold moment
  rw [gamma_sample_eq T i (by omega) hi]
  convert h using 1
  unfold sampleTime sampleIndex RHBatch01RawChirpedInput.value
  push_cast
  ring
end RHHighSamplingFunctions
end
end RHFastKernelUniformGammaFFT
open scoped FourierTransform
theorem solution (T : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (k : Nat) (hk:k<26)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hinput:∀ j:Fin 16384,
      let m:=RHFastKernelMomentArithmetic.moment j.val (RHFastKernelGammaArithmetic.compute T j.val) k
      let c:=RHHighFFTArithmeticBase.chirp j.val
      (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (m : Fin 2048) (hm:m.val≤1953) :
    ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) ((m.val:ℝ)/512)-
      Complex.exp (((2*Real.pi*((m.val:ℝ)/2):ℝ):ℂ)*Complex.I)*((1/32:ℂ)*
        (let v:=((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[m.val]?).getD (0,0)
         ((v.1:ℂ)+(v.2:ℂ)*Complex.I)/(2:ℂ)^80))‖≤1/10^15 := by
  have hs (i:Fin 16384):
      ‖RHHighSamplingFunctions.moment (T:ℝ) k (RHHighSamplingFunctions.sampleTime i.val)-
        RHFastKernelUniformGammaFFT.RHBatch01RawChirpedInput.value (RHFastKernelMomentArithmetic.moment i.val
          (RHFastKernelGammaArithmetic.compute T i.val) k)‖≤1/10^23 :=
    RHFastKernelUniformGammaFFT.RHHighSamplingFunctions.moment_enclosure T i.val k hT hU i.isLt hk
  exact RHFastKernelUniformGammaFFT.RHBatch01GammaDFTBridge.fourier_from_arrays T hT hU k hk ar ai br bi hAr hAi hBr hBi hs hinput hkernel m hm
#print axioms solution
