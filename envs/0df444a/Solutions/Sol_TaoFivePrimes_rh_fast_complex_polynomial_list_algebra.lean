-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_complex_polynomial_list_algebra
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:31:36.308003+00:00
-- url     : https://prove2.me/submissions/429604af-95f2-419b-abab-eef352d3fe24

import Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset Polynomial
namespace RHFastComplexPolynomialListProof
open RHFastComplexPoly
lemma entry_none (xs:List ℂ) (k:Nat) (hk:xs.length≤k) : entry xs k=0 := by
 simp only [entry,List.getElem?_eq_none hk,Option.getD_none]
lemma entry_tabulate (f:Nat→ℂ) (n k:Nat) (hk:k<n) :
 entry ((List.range n).map f) k=f k := by
 simp only [entry,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
lemma coeff_polynomial (xs:List ℂ) (k:Nat) : (polynomial xs).coeff k=entry xs k := by
 unfold polynomial
 rw [Polynomial.finsetSum_coeff]
 simp only [Polynomial.coeff_C_mul_X_pow]
 by_cases hk:k<xs.length
 · simpa only [Finset.sum_ite_eq,Finset.mem_range,if_pos hk]
 · rw [entry_none xs k (by omega)]
   simpa only [Finset.sum_ite_eq,Finset.mem_range,if_neg hk]
lemma entry_add (xs ys:List ℂ) (k:Nat) : entry (addList xs ys) k=entry xs k+entry ys k := by
 by_cases hk:k<max xs.length ys.length
 · exact entry_tabulate _ _ _ hk
 · have hx:xs.length≤k:=by omega
   have hy:ys.length≤k:=by omega
   have ho:(addList xs ys).length≤k:=by simp only [addList,List.length_map,List.length_range];omega
   rw [entry_none _ _ ho,entry_none _ _ hx,entry_none _ _ hy]
   ring
lemma polynomial_add (xs ys:List ℂ) : polynomial (addList xs ys)=polynomial xs+polynomial ys := by
 ext k
 rw [Polynomial.coeff_add,coeff_polynomial,coeff_polynomial,coeff_polynomial,entry_add]
lemma polynomial_mul (xs ys:List ℂ) : polynomial (mulList xs ys)=polynomial xs*polynomial ys := by
 ext k
 rw [coeff_polynomial,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 simp only [coeff_polynomial]
 by_cases hk:k<xs.length+ys.length-1
 · change entry ((List.range (xs.length+ys.length-1)).map (mulCoeff xs ys)) k=_
   rw [entry_tabulate _ _ _ hk]
   unfold mulCoeff
   apply Finset.sum_congr rfl
   intro i hi
   have hik:i≤k:=by have :=Finset.mem_range.mp hi;omega
   by_cases hx:i<xs.length
   · by_cases hy:k-i<ys.length
     · simp only [hx,hy,hik,and_self,ite_true]
     · rw [entry_none ys (k-i) (by omega)]
       simp only [hy,and_false,ite_false,mul_zero]
   · rw [entry_none xs i (by omega)]
     simp only [hx,false_and,ite_false,zero_mul]
 · have ho:(mulList xs ys).length≤k:=by simp only [mulList,List.length_map,List.length_range];omega
   rw [entry_none _ _ ho]
   symm
   apply Finset.sum_eq_zero
   intro i hi
   have hik:i≤k:=by have :=Finset.mem_range.mp hi;omega
   by_cases hx:i<xs.length
   · have hy:ys.length≤k-i:=by omega
     rw [entry_none ys (k-i) hy,mul_zero]
   · rw [entry_none xs i (by omega),zero_mul]
lemma entry_divide (xs:List ℂ) (n k:Nat) : entry (divideList xs n) k=entry xs k/(n:ℂ) := by
 unfold entry divideList
 rw [List.getElem?_map]
 cases h:xs[k]? <;> simp [h]
lemma polynomial_divide (xs:List ℂ) (n:Nat) :
 polynomial (divideList xs n)=polynomial xs*Polynomial.C ((n:ℂ)⁻¹) := by
 ext k
 rw [Polynomial.coeff_mul_C,coeff_polynomial,coeff_polynomial,entry_divide]
 exact div_eq_mul_inv _ _
lemma polynomial_singleton (a:ℂ) : polynomial [a]=Polynomial.C a := by
 ext k
 rw [coeff_polynomial,Polynomial.coeff_C]
 cases k with
 | zero=>simp [entry]
 | succ k=>simp [entry]
end RHFastComplexPolynomialListProof

theorem solution (xs ys:List ℂ) (n:Nat) :
 RHFastComplexPoly.polynomial (RHFastComplexPoly.addList xs ys)=
   RHFastComplexPoly.polynomial xs+RHFastComplexPoly.polynomial ys ∧
 RHFastComplexPoly.polynomial (RHFastComplexPoly.mulList xs ys)=
   RHFastComplexPoly.polynomial xs*RHFastComplexPoly.polynomial ys ∧
 RHFastComplexPoly.polynomial (RHFastComplexPoly.divideList xs n)=
   RHFastComplexPoly.polynomial xs*Polynomial.C ((n:ℂ)⁻¹) :=
 ⟨RHFastComplexPolynomialListProof.polynomial_add xs ys,
  RHFastComplexPolynomialListProof.polynomial_mul xs ys,
  RHFastComplexPolynomialListProof.polynomial_divide xs n⟩
#print axioms solution
