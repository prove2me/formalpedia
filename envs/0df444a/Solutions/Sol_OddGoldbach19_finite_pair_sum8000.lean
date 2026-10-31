-- Prove2me | solution 1 for OddGoldbach19.finite_pair_sum8000
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:52:13.985588+00:00
-- url     : https://prove2.me/submissions/9cddc606-160a-4df2-8735-98c43c36f2b2

import Mathlib
import Theorems.Thm_OddGoldbach19_prime_family8000
import Theorems.Thm_OddGoldbach19_packed_prime_factors8000
import Theorems.Thm_OddGoldbach19_packed_weight_factor8000
import Theorems.Thm_OddGoldbach19_packed_numeric8000
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Finset
namespace PolynomialPacking

theorem coeff_ofDigits (L : List ℕ) (k : ℕ) :
    (Nat.ofDigits (X:ℕ[X]) L).coeff k=L.getD k 0 := by
  induction L generalizing k with
  | nil => simp [Nat.ofDigits]
  | cons a L ih =>
    cases k with
    | zero => simp [Nat.ofDigits,coeff_add,coeff_mul,ih]
    | succ k =>
      change ((a:ℕ[X])+X*Nat.ofDigits (X:ℕ[X]) L).coeff (k+1)=_
      simp [coeff_add,coeff_X_mul,ih]

theorem eval_ofDigits (L : List ℕ) (b : ℕ) :
    (Nat.ofDigits (X:ℕ[X]) L).eval b=Nat.ofDigits b L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons a L ih => simp [Nat.ofDigits,ih]

theorem coefficient_le_eval_one (P : ℕ[X]) (k : ℕ) : P.coeff k≤P.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow,mul_one]
  by_cases hk : k<P.natDegree+1
  · exact single_le_sum (fun i _=>Nat.zero_le _) (mem_range.mpr hk)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Nat.zero_le _

theorem as_ofDigits (P : ℕ[X]) :
    Nat.ofDigits (X:ℕ[X]) ((List.range (P.natDegree+1)).map P.coeff)=P := by
  ext k
  rw [coeff_ofDigits]
  by_cases hk : k<P.natDegree+1
  · simp [List.getD_eq_getElem?_getD,hk]
  · simp [List.getD_eq_getElem?_getD,hk,
      coeff_eq_zero_of_natDegree_lt (show P.natDegree<k by omega)]

theorem digit_extract (L : List ℕ) (b k : ℕ) (hb : 0<b)
    (hL : ∀ d∈L,d<b) :
    (Nat.ofDigits b L/b^k)%b=L.getD k 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop k hb L hL,Nat.ofDigits_mod_eq_head!]
  have he : (L.drop k).head!=L.getD k 0 := by
    simp [List.head!_eq_head?_getD,List.getD_eq_getElem?_getD]
  rw [he]
  by_cases hk : k<L.length
  · apply Nat.mod_eq_of_lt
    simpa [List.getD_eq_getElem?_getD,hk] using hL _ (List.getElem_mem hk)
  · simp [List.getD_eq_getElem?_getD,hk]

theorem extract_coefficient (P : ℕ[X]) (b k : ℕ) (hb : 0<b)
    (hP : P.eval 1<b) : (P.eval b/b^k)%b=P.coeff k := by
  let L : List ℕ := (List.range (P.natDegree+1)).map P.coeff
  have he : Nat.ofDigits (X:ℕ[X]) L=P := as_ofDigits P
  have hd : ∀ d∈L,d<b := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
    exact (coefficient_le_eval_one P i).trans_lt hP
  have hv : Nat.ofDigits b L=P.eval b := by rw [←eval_ofDigits,he]
  rw [←hv,digit_extract L b k hb hd,←coeff_ofDigits L k,he]
end PolynomialPacking
#print axioms PolynomialPacking.extract_coefficient
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Finset
namespace PolynomialPacking

noncomputable def shiftPoly (L : List ℕ) (f : ℕ→ℕ) : ℕ[X] :=
  (L.map fun a=>monomial (f a) 1).sum

noncomputable def weightPoly (D : ℕ) (w : ℕ→ℕ) : ℕ[X] :=
  ∑ d∈Icc 1 D, monomial (D-d) (w d)

lemma shiftPoly_nil (f : ℕ→ℕ) : shiftPoly [] f=0 := by simp [shiftPoly]
lemma shiftPoly_cons (a : ℕ) (L : List ℕ) (f : ℕ→ℕ) :
    shiftPoly (a::L) f=monomial (f a) 1+shiftPoly L f := by simp [shiftPoly]

theorem monomial_pair_coefficient (a b D : ℕ) (ha : a≤D) (hb : b≤D) (w : ℕ→ℕ) :
    ((monomial a 1*monomial (D-b) 1)*weightPoly D w).coeff (2*D)=
      if b<a then w (a-b) else 0 := by
  unfold weightPoly
  rw [mul_sum]
  simp only [finsetSum_coeff,monomial_mul_monomial,one_mul]
  simp only [coeff_monomial]
  by_cases hab : b<a
  · rw [if_pos hab]
    have hd : a-b∈Icc 1 D := by simp only [mem_Icc];omega
    rw [sum_eq_single (a-b)]
    · rw [if_pos (by omega)]
    · intro d hd hne
      have hdd := mem_Icc.mp hd
      rw [if_neg (by omega)]
    · exact fun hh=>(hh hd).elim
  · rw [if_neg hab]
    apply sum_eq_zero
    intro d hd
    have hdd := mem_Icc.mp hd
    rw [if_neg (by omega)]

theorem row_coefficient (a D : ℕ) (ha : a≤D) (w : ℕ→ℕ) (J : List ℕ) :
    (∀ b∈J,b≤D) →
    (monomial a 1*shiftPoly J (fun b=>D-b)*weightPoly D w).coeff (2*D)=
      (J.map fun b=>if b<a then w (a-b) else 0).sum := by
  induction J with
  | nil => intro _;simp [shiftPoly_nil]
  | cons b J ih =>
    intro hJ
    rw [shiftPoly_cons,mul_add,add_mul,coeff_add,
      monomial_pair_coefficient a b D ha (hJ b (by simp)) w]
    rw [ih (fun b hb=>hJ b (List.mem_cons_of_mem _ hb))]
    simp only [List.map_cons,List.sum_cons]

theorem pair_coefficient (I J : List ℕ) (D : ℕ) (w : ℕ→ℕ) :
    (∀ a∈I,a≤D) → (∀ b∈J,b≤D) →
    (shiftPoly I id*shiftPoly J (fun b=>D-b)*weightPoly D w).coeff (2*D)=
      (I.map fun a=>(J.map fun b=>if b<a then w (a-b) else 0).sum).sum := by
  induction I with
  | nil => intro _ _;simp [shiftPoly_nil]
  | cons a I ih =>
    intro hI hJ
    rw [shiftPoly_cons,add_mul,add_mul,coeff_add]
    change (monomial a 1*shiftPoly J (fun b=>D-b)*weightPoly D w).coeff (2*D)+_= _
    rw [row_coefficient a D (hI a (by simp)) w J hJ]
    rw [ih (fun a ha=>hI a (List.mem_cons_of_mem _ ha)) hJ]
    simp only [List.map_cons,List.sum_cons]
end PolynomialPacking
#print axioms PolynomialPacking.pair_coefficient
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open scoped BigOperators
open Polynomial Finset PolynomialPacking
namespace PrimePairPacking

def positions (L : List ℕ) : List ℕ := L.map fun p=>(p-3)/2
noncomputable def P (L : List ℕ) (D : ℕ) (w : ℕ→ℕ) : ℕ[X] :=
  shiftPoly (positions L) id*shiftPoly (positions L) (fun b=>D-b)*weightPoly D w
def pairSum (L : List ℕ) (w : ℕ→ℕ) : ℕ :=
  (L.map fun a=>(L.map fun b=>if b<a then w ((a-b)/2) else 0).sum).sum

theorem pairSum_coefficient (L : List ℕ) (D : ℕ) (w : ℕ→ℕ)
    (hL : ∀ q∈L,3≤q ∧ q%2=1 ∧ (q-3)/2≤D) :
    (P L D w).coeff (2*D)=pairSum L w := by
  have hpos : ∀ a∈positions L,a≤D := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    exact (hL q hq).2.2
  rw [P,pair_coefficient (positions L) (positions L) D w hpos hpos]
  simp only [positions,List.map_map,Function.comp_apply,id_eq]
  unfold pairSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have hap := hL a ha
  have hbp := hL b hb
  have he : ((b-3)/2<(a-3)/2) ↔ b<a := by omega
  change (if (b-3)/2<(a-3)/2 then w ((a-3)/2-(b-3)/2) else 0)=_
  by_cases hba : b<a
  · rw [if_pos (he.mpr hba),if_pos hba]
    congr 1
    omega
  · rw [if_neg (fun hh=>hba (he.mp hh)),if_neg hba]

lemma eval_shiftPoly (L : List ℕ) (f : ℕ→ℕ) (b : ℕ) :
    (shiftPoly L f).eval b=(L.map fun a=>b^(f a)).sum := by
  induction L with
  | nil => simp [shiftPoly_nil]
  | cons a L ih => simp [shiftPoly_cons,ih]

lemma eval_shiftPoly_one (L : List ℕ) (f : ℕ→ℕ) :
    (shiftPoly L f).eval 1=L.length := by rw [eval_shiftPoly];simp

lemma eval_weightPoly (D : ℕ) (w : ℕ→ℕ) (b : ℕ) :
    (weightPoly D w).eval b=∑ d∈Icc 1 D,w d*b^(D-d) := by
  rw [weightPoly,eval_finsetSum]
  apply sum_congr rfl
  intro d hd
  simp

theorem eval_one_bound (L : List ℕ) (D M : ℕ) (w : ℕ→ℕ) (hw : ∀ d,w d≤M) :
    (P L D w).eval 1≤L.length*L.length*(D*M) := by
  rw [P,eval_mul,eval_mul,eval_shiftPoly_one,eval_shiftPoly_one]
  simp only [positions,List.length_map]
  apply Nat.mul_le_mul_left
  rw [eval_weightPoly]
  simp only [one_pow,mul_one]
  calc
    ∑ d∈Icc 1 D,w d≤∑ _d∈Icc 1 D,M := sum_le_sum (fun d _=>hw d)
    _ =D*M := by simp

def qEval (L : List ℕ) (b : ℕ) : ℕ := ((positions L).map fun a=>b^a).sum
def reverseEval (L : List ℕ) (D b : ℕ) : ℕ := ((positions L).map fun a=>b^(D-a)).sum
def weightEval (D : ℕ) (w : ℕ→ℕ) (b : ℕ) : ℕ :=∑ d∈Icc 1 D,w d*b^(D-d)

theorem pairSum_as_digit (L : List ℕ) (D M b : ℕ) (w : ℕ→ℕ)
    (hL : ∀ q∈L,3≤q ∧ q%2=1 ∧ (q-3)/2≤D) (hw : ∀ d,w d≤M)
    (hb : 0<b) (hbig : L.length*L.length*(D*M)<b) :
    pairSum L w=((qEval L b*reverseEval L D b*weightEval D w b)/b^(2*D))%b := by
  have hp : (P L D w).eval 1<b := (eval_one_bound L D M w hw).trans_lt hbig
  rw [←pairSum_coefficient L D w hL,←extract_coefficient (P L D w) b (2*D) hb hp]
  simp only [P,eval_mul,eval_shiftPoly,eval_weightPoly,qEval,reverseEval,weightEval,id_eq]

open OddGoldbach19.Cert8000
attribute [local irreducible] Qlist WP
theorem concrete_pairSum_as_digit :
    pairSum Qlist WP=((qEval Qlist (2^64)*reverseEval Qlist 40907 (2^64)*
      weightEval 40907 WP (2^64))/(2^64)^(2*40907))%(2^64) := by
  apply pairSum_as_digit Qlist 40907 65535 (2^64) WP
  · intro q hq
    have hh := OddGoldbach19.prime_family8000.1 q hq
    have hlo := hh.1.two_le
    have ho := Nat.odd_iff.mp (hh.1.odd_of_ne_two hh.2.1)
    omega
  · intro d
    have hh : WP d<65536 := by unfold WP;exact Nat.mod_lt _ (by decide)
    omega
  · norm_num
  · rw [OddGoldbach19.prime_family8000.2.2]
    norm_num
end PrimePairPacking
#print axioms PrimePairPacking.pairSum_as_digit
#print axioms PrimePairPacking.concrete_pairSum_as_digit
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open OddGoldbach19.Cert8000 OddGoldbach19.Packed8000
namespace OddGoldbach19
attribute [local irreducible] Cert8000.Qlist Cert8000.WP
  PrimePairPacking.pairSum packedQ packedR packedW

theorem finite_pair_sum_exact8000 :
    PrimePairPacking.pairSum Qlist WP=557349373474 := by
  have hh := PrimePairPacking.concrete_pairSum_as_digit
  have hq : PrimePairPacking.qEval Qlist (2^64)=packedQ := by
    simpa only [PrimePairPacking.qEval,PrimePairPacking.positions,List.map_map,Function.comp_def]
      using OddGoldbach19.packed_prime_factors8000.1
  have hr : PrimePairPacking.reverseEval Qlist 40907 (2^64)=packedR := by
    simpa only [PrimePairPacking.reverseEval,PrimePairPacking.positions,List.map_map,Function.comp_def]
      using OddGoldbach19.packed_prime_factors8000.2
  have hw : PrimePairPacking.weightEval 40907 WP (2^64)=packedW := OddGoldbach19.packed_weight_factor8000
  rw [hq,hr,hw] at hh
  exact hh.trans packed_numeric8000

theorem finite_pair_sum8000 :
    (Qlist.map fun a=>(Qlist.map fun b=>if b<a then WP ((a-b)/2) else 0).sum).sum≤557349373474 := by
  have hh := finite_pair_sum_exact8000.le
  unfold PrimePairPacking.pairSum at hh
  exact hh
end OddGoldbach19
#print axioms OddGoldbach19.finite_pair_sum8000
theorem solution :
    (OddGoldbach19.Cert8000.Qlist.map fun a=>(OddGoldbach19.Cert8000.Qlist.map fun b=>
      if b<a then OddGoldbach19.Cert8000.WP ((a-b)/2) else 0).sum).sum≤557349373474 :=
  OddGoldbach19.finite_pair_sum8000
#print axioms solution
