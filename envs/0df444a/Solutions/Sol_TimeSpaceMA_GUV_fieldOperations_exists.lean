-- Prove2me | solution 1 for TimeSpaceMA.GUV.fieldOperations_exists
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:31:21.773473+00:00
-- url     : https://prove2.me/submissions/6f07e00c-9de8-4f5a-a9c6-6c5bde83d1fe

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
import Definitions.Def_TimeSpaceMA_GUVFieldOperations
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Ring


open scoped BigOperators

namespace TimeSpaceMA.GUV
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Polynomial

namespace BinaryFieldArithmetic

variable {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)

def radix (a n : ℕ) := 2^(2*halfSeed a n)

theorem radix_pos (a n : ℕ) : 0 < radix a n := by unfold radix; positivity

def clip (a n w : ℕ) : ℕ := w % radix a n

def word (a n w : ℕ) : FieldWord a n := ⟨clip a n w, Nat.mod_lt _ (radix_pos ..)⟩

theorem clip_bound (a n u : ℕ) : clip a n u < radix a n :=
  Nat.mod_lt _ (radix_pos ..)

theorem clip_eq (a n u : ℕ) (hu : u < radix a n) : clip a n u = u :=
  Nat.mod_eq_of_lt hu

theorem size_le_of_lt {u a n : ℕ} (hu : u < radix a n) :
    u.size ≤ 2*halfSeed a n := Nat.size_le.mpr hu

theorem word_val (a n w : ℕ) (hw : w < radix a n) :
    (word a n w).val = w := clip_eq a n w hw

theorem native_halfSeed {α : Type} {enc : α ↪ List Bool} (a : ℕ) {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => halfSeed a (n x)) enc encUnary := by
  let hb := (binary_le' (const 1) (unary_to_binary.comp hn))
  have hm : ComputableTidilyInPolyTime (fun x => max 1 (n x)) enc encUnary := by
    apply (hb.ite_decide hn (const 1)).of_enc_eq
    intro x
    by_cases h : 1 ≤ n x
    · simp [h, max_eq_right h]
    · simp [h, max_eq_left (by omega : n x ≤ 1)]
  exact unary_mul.comp ((const a).prod
    (ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hm)))


end BinaryFieldArithmetic
end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV

open Polynomial

/-- The little-endian bit vector of an integer as a polynomial over the two-element field. -/
noncomputable def binaryLowerPoly (e x : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range e, monomial i ((x / 2^i % 2 : ℕ) : ZMod 2)

/-- A natural number codes the lower coefficients of a monic polynomial. -/
noncomputable def binaryMonicPoly (e x : ℕ) : (ZMod 2)[X] :=
  X^e + binaryLowerPoly e x

theorem coeff_binaryLower (e x i : ℕ) :
    (binaryLowerPoly e x).coeff i = if i < e then ((x / 2^i % 2 : ℕ) : ZMod 2) else 0 := by
  classical
  unfold binaryLowerPoly
  simp only [finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp

theorem binaryLower_degree_lt (e x : ℕ) : (binaryLowerPoly e x).degree < e := by
  classical
  unfold binaryLowerPoly
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  exact (degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))

theorem binaryMonicPoly_monic (e x : ℕ) : (binaryMonicPoly e x).Monic :=
  monic_X_pow_add (binaryLower_degree_lt e x)

@[simp] theorem binaryMonicPoly_natDegree (e x : ℕ) : (binaryMonicPoly e x).natDegree = e := by
  unfold binaryMonicPoly
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact binaryLower_degree_lt e x

private theorem coeff_binaryMonic_lt {e x i : ℕ} (hi : i < e) :
    (binaryMonicPoly e x).coeff i = ((x / 2^i % 2 : ℕ) : ZMod 2) := by
  simp [binaryMonicPoly,coeff_binaryLower,hi,show i ≠ e by omega]

/-- Given lower coefficients as residues, view their binary digits as one finite index. -/
noncomputable def lowerCoeffCode (p : (ZMod 2)[X]) (e : ℕ) : Fin (2^e) :=
  finFunctionFinEquiv (fun i : Fin e => (ZMod.finEquiv 2).symm (p.coeff i.val))

private theorem lowerCoeffCode_digit (p : (ZMod 2)[X]) (e : ℕ) (j : Fin e) :
    ((((lowerCoeffCode p e).val / 2^j.val) % 2 : ℕ) : ZMod 2) = p.coeff j.val := by
  have he : (finFunctionFinEquiv (m := 2) (n := e)).symm (lowerCoeffCode p e) j =
      (ZMod.finEquiv 2).symm (p.coeff j.val) := by simp [lowerCoeffCode]
  have hv := congrArg Fin.val he
  change (lowerCoeffCode p e).val / 2^j.val % 2 = (p.coeff j.val).val at hv
  rw [hv]
  exact ZMod.natCast_zmod_val _

/-- Every monic degree-`e` polynomial over `ZMod 2` has this finite binary presentation. -/
theorem binaryMonicPoly_of_monic {p : (ZMod 2)[X]} (hp : p.Monic) (e : ℕ)
    (he : p.natDegree = e) : binaryMonicPoly e (lowerCoeffCode p e).val = p := by
  ext i
  by_cases hl : i < e
  · rw [coeff_binaryMonic_lt hl]
    exact lowerCoeffCode_digit p e ⟨i,hl⟩
  by_cases hh : i = e
  · subst i
    calc
      (binaryMonicPoly e (lowerCoeffCode p e).val).coeff e = 1 := by
        have H := (binaryMonicPoly_monic e (lowerCoeffCode p e).val).coeff_natDegree
        rw [binaryMonicPoly_natDegree] at H
        exact H
      _ = p.coeff e := by simpa only [he] using hp.coeff_natDegree.symm
  · have hgt : e < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hgt), coeff_eq_zero_of_natDegree_lt (he ▸ hgt)]

/-- The quotient search has a witness in each positive degree; take the minimal polynomial
of a primitive element of the finite extension furnished by `GaloisField`. -/
theorem exists_binaryMonicPoly_irreducible (e : ℕ) (he : 0 < e) :
    ∃ x : Fin (2^e), Irreducible (binaryMonicPoly e x.val) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 e
  obtain ⟨x,hx⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) F
  have hInt : IsIntegral (ZMod 2) x := Algebra.IsIntegral.isIntegral x
  have hdeg : (minpoly (ZMod 2) x).natDegree = e := by
    rw [← IntermediateField.adjoin.finrank hInt, hx, IntermediateField.finrank_top', GaloisField.finrank 2 he.ne']
  refine ⟨lowerCoeffCode (minpoly (ZMod 2) x) e,?_⟩
  rw [binaryMonicPoly_of_monic (minpoly.monic hInt) e hdeg]
  exact minpoly.irreducible hInt

private theorem zmod2_nonzero_eq_one {r : ZMod 2} (hr : r ≠ 0) : r = 1 := by
  have h := ZMod.val_lt r
  have hz : r.val ≠ 0 := fun he => hr ((ZMod.val_eq_zero r).mp he)
  apply ZMod.val_injective 2
  rw [show (1 : ZMod 2).val = 1 by decide]
  omega

/-- Reducibility of a monic positive-degree binary polynomial is equivalent to being
one of the products obtained by enumerating all proper positive degree splits. -/
theorem binaryMonicPoly_irreducible_iff_no_factor {e x : ℕ} (he : 0 < e) :
    Irreducible (binaryMonicPoly e x) ↔
      ∀ (d : ℕ), 0 < d → d < e → ∀ (u : Fin (2^d)) (v : Fin (2^(e-d))),
        binaryMonicPoly e x ≠ binaryMonicPoly d u.val * binaryMonicPoly (e-d) v.val := by
  have hPnot : ¬ IsUnit (binaryMonicPoly e x) := by
    intro hi
    have hz := natDegree_eq_zero_of_isUnit hi
    rw [binaryMonicPoly_natDegree] at hz
    omega
  rw [irreducible_iff]
  constructor
  · rintro ⟨_,hf⟩ d hd hde u v heq
    have h := hf heq
    rcases h with h | h
    · have hh := natDegree_eq_zero_of_isUnit h
      rw [binaryMonicPoly_natDegree] at hh
      omega
    · have hh := natDegree_eq_zero_of_isUnit h
      rw [binaryMonicPoly_natDegree] at hh
      omega
  · intro hf
    refine ⟨hPnot,?_⟩
    intro p q hpq
    by_contra! hu
    have hpn : p ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at hpq
      exact (binaryMonicPoly_monic e x).ne_zero hpq
    have hqn : q ≠ 0 := by
      intro hz
      rw [hz,mul_zero] at hpq
      exact (binaryMonicPoly_monic e x).ne_zero hpq
    have hpm : p.Monic := zmod2_nonzero_eq_one (leadingCoeff_ne_zero.mpr hpn)
    have hqm : q.Monic := zmod2_nonzero_eq_one (leadingCoeff_ne_zero.mpr hqn)
    have hp' : 0 < p.natDegree := hpm.natDegree_pos.mpr (fun h => hu.1 (h ▸ isUnit_one))
    have hq' : 0 < q.natDegree := hqm.natDegree_pos.mpr (fun h => hu.2 (h ▸ isUnit_one))
    have hdeg : e = p.natDegree + q.natDegree := by
      rw [← binaryMonicPoly_natDegree e x, hpq, hpm.natDegree_mul hqm]
    have hqdeg : q.natDegree = e-p.natDegree := by omega
    exact hf p.natDegree hp' (by omega) (lowerCoeffCode p _) (lowerCoeffCode q _)
      (by rw [binaryMonicPoly_of_monic hpm _ rfl, binaryMonicPoly_of_monic hqm _ hqdeg, hpq])

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV

open Polynomial

/-- The quotient-residue shift by one binary digit, i.e. multiplication by the variable. -/
def wordMulX (e f x : ℕ) : ℕ :=
  (2*x) % 2^e ^^^ (if x.testBit (e-1) then f % 2^e else 0)

/-- One shift-and-add round for characteristic two. -/
def wordMulStep (e f y : ℕ) (i : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  (wordMulX e f s.1, if y.testBit i then s.2 ^^^ s.1 else s.2)

/-- Multiplication of bit polynomials, reducing modulo the monic polynomial of width `e`. -/
def wordMul (e f x y : ℕ) : ℕ :=
  ((List.range e).foldl (fun s i => wordMulStep e f y i s) (x % 2^e,0)).2

private theorem divbit_eq_test (x i : ℕ) : x / 2^i % 2 = (x.testBit i).toNat :=
  (Nat.toNat_testBit x i).symm

private theorem cast_testBit_xor (a b i : ℕ) :
    (((a ^^^ b).testBit i).toNat : ZMod 2) = ((a.testBit i).toNat : ZMod 2) + ((b.testBit i).toNat : ZMod 2) := by
  rw [Nat.testBit_xor]
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> decide

@[simp] theorem binaryLowerPoly_zero (e : ℕ) : binaryLowerPoly e 0 = 0 := by
  ext i
  simp [coeff_binaryLower]

/-- XOR of words is addition of the encoded polynomials. -/
theorem binaryLowerPoly_xor (e a b : ℕ) :
    binaryLowerPoly e (a ^^^ b) = binaryLowerPoly e a + binaryLowerPoly e b := by
  ext i
  by_cases h : i < e
  · simpa only [coeff_binaryLower,if_pos h,coeff_add,divbit_eq_test] using cast_testBit_xor a b i
  · simp [coeff_binaryLower,h]

/-- Clipping to the number of represented coefficients has no algebraic effect. -/
theorem binaryLowerPoly_mod (e a : ℕ) : binaryLowerPoly e (a % 2^e) = binaryLowerPoly e a := by
  ext i
  by_cases h : i < e
  · simp only [coeff_binaryLower,if_pos h,divbit_eq_test,Nat.testBit_mod_two_pow,decide_eq_true h,Bool.true_and]
  · simp [coeff_binaryLower,h]

private theorem binaryLowerPoly_shift_identity (e x : ℕ) (he : 0 < e) :
    binaryLowerPoly e (2*x) + monomial e ((x.testBit (e-1)).toNat : ZMod 2) =
      X * binaryLowerPoly e x := by
  ext i
  rw [coeff_add]
  cases i with
  | zero =>
    simp [coeff_binaryLower,coeff_monomial,show 0 < e by omega,show e ≠ 0 by omega]
  | succ i =>
    rw [coeff_X_mul]
    have b : (2*x).testBit (i+1) = x.testBit i := by
      rw [show 2*x = x <<< 1 by simp [Nat.shiftLeft_eq,Nat.mul_comm],Nat.testBit_shiftLeft]
      simp
    by_cases h : i+1 < e
    · have hi : i < e := by omega
      simp [coeff_binaryLower,coeff_monomial,h,hi,show e ≠ i+1 by omega,divbit_eq_test,b]
    · by_cases hv : i+1 = e
      · have hi : i < e := by omega
        simp [coeff_binaryLower,hv,hi,divbit_eq_test,show e-1=i by omega]
      · have hi : ¬ i < e := by omega
        simp [coeff_binaryLower,coeff_monomial,h,Ne.symm hv,hi]

/-- The quotient representative of a bit polynomial. -/
noncomputable def wordValue (e f x : ℕ) : AdjoinRoot (binaryMonicPoly e f) :=
  AdjoinRoot.mk (binaryMonicPoly e f) (binaryLowerPoly e x)

private theorem wordCharP (e f : ℕ) (he : 0 < e) : CharP (AdjoinRoot (binaryMonicPoly e f)) 2 := by
  have hf : (binaryMonicPoly e f).degree ≠ 0 := by
    rw [degree_eq_natDegree (binaryMonicPoly_monic e f).ne_zero, binaryMonicPoly_natDegree]
    exact_mod_cast he.ne'
  let := AdjoinRoot.nontrivial (binaryMonicPoly e f) hf
  exact CharP.of_ringHom_of_ne_zero (AdjoinRoot.of _) 2 (by decide)

/-- Smallness of result after multiplying by the variable. -/
theorem wordMulX_lt (e f x : ℕ) : wordMulX e f x < 2^e := by
  apply Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact Nat.two_pow_pos _

/-- Multiplying by the variable is one shift and a conditional XOR of the modulus. -/
theorem wordValue_wordMulX (e f x : ℕ) (he : 0 < e) :
    wordValue e f (wordMulX e f x) = AdjoinRoot.root _ * wordValue e f x := by
  let F := AdjoinRoot (binaryMonicPoly e f)
  let : CharP F 2 := wordCharP e f he
  let φ := AdjoinRoot.mk (binaryMonicPoly e f)
  have h_monic : φ (binaryMonicPoly e f) = 0 := by simp [φ]
  have hneg : φ (X^e) = φ (binaryLowerPoly e f) := by
    have hh : φ (X^e) + φ (binaryLowerPoly e f) = 0 := by
      rw [← φ.map_add]
      exact h_monic
    calc
      φ (X^e) = -φ (binaryLowerPoly e f) := eq_neg_of_add_eq_zero_left hh
      _ = _ := CharTwo.neg_eq _
  have hid := congrArg φ (binaryLowerPoly_shift_identity e x he)
  simp only [map_add,map_mul] at hid
  have hX : φ X = AdjoinRoot.root (binaryMonicPoly e f) := AdjoinRoot.mk_X
  rw [hX] at hid
  unfold wordMulX wordValue
  rw [binaryLowerPoly_xor,binaryLowerPoly_mod,map_add]
  change φ (binaryLowerPoly e (2*x)) + φ (binaryLowerPoly e _) = _
  rw [← hid]
  have heq : φ (binaryLowerPoly e (if x.testBit (e-1) then f % 2^e else 0)) =
      φ (monomial e ((x.testBit (e-1)).toNat : ZMod 2)) := by
    cases h : x.testBit (e-1)
    · simp [φ]
    · simp only [if_true,Bool.toNat_true,Nat.cast_one,binaryLowerPoly_mod,monomial_one_right_eq_X_pow]
      exact hneg.symm
  exact congrArg (fun z => φ (binaryLowerPoly e (2*x)) + z) heq

@[simp] theorem wordValue_zero (e f : ℕ) : wordValue e f 0 = 0 := by simp [wordValue]

theorem wordValue_xor (e f a b : ℕ) : wordValue e f (a ^^^ b) = wordValue e f a + wordValue e f b := by
  simp [wordValue,binaryLowerPoly_xor]

theorem wordValue_mod (e f a : ℕ) : wordValue e f (a % 2^e) = wordValue e f a := by
  simp [wordValue,binaryLowerPoly_mod]

private theorem wordMulStep_bound (e f y i : ℕ) (s : ℕ × ℕ)
    (h₁ : s.1 < 2^e) (h₂ : s.2 < 2^e) :
    (wordMulStep e f y i s).1 < 2^e ∧ (wordMulStep e f y i s).2 < 2^e := by
  refine ⟨wordMulX_lt ..,?_⟩
  unfold wordMulStep
  dsimp only
  split
  · exact Nat.xor_lt_two_pow h₂ h₁
  · exact h₂

private theorem wordMul_fold_bound (e f y : ℕ) (s : ℕ × ℕ) (js : List ℕ)
    (h₁ : s.1 < 2^e) (h₂ : s.2 < 2^e) :
    let r := js.foldl (fun p i => wordMulStep e f y i p) s
    r.1 < 2^e ∧ r.2 < 2^e := by
  induction js generalizing s with
  | nil => exact ⟨h₁,h₂⟩
  | cons i js ih =>
    exact ih _ (wordMulStep_bound e f y i s h₁ h₂).1 (wordMulStep_bound e f y i s h₁ h₂).2

/-- Every product remains in the coded field's canonical width. -/
theorem wordMul_lt (e f x y : ℕ) : wordMul e f x y < 2^e :=
  (wordMul_fold_bound e f y _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)).2

private theorem wordMul_fold_spec (e f y : ℕ) (he : 0 < e) (s : ℕ × ℕ) (j k : ℕ) :
    let out := (List.range' j k).foldl (fun p i => wordMulStep e f y i p) s
    let X := AdjoinRoot.root (binaryMonicPoly e f)
    wordValue e f out.1 = X^k*wordValue e f s.1 ∧
      wordValue e f out.2 = wordValue e f s.2 +
        (∑ i ∈ Finset.range k, (if y.testBit (j+i) then X^i else 0)) * wordValue e f s.1 := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,Nat.one_mul]
    let mid := (List.range' j k).foldl (fun p i => wordMulStep e f y i p) s
    let root := AdjoinRoot.root (binaryMonicPoly e f)
    obtain ⟨h₁,h₂⟩ := ih s
    change wordValue e f mid.1 = root^k*wordValue e f s.1 at h₁
    change wordValue e f mid.2 = _ at h₂
    constructor
    · change wordValue e f (wordMulX e f mid.1) = root^(k+1)*wordValue e f s.1
      rw [wordValue_wordMulX e f _ he,h₁,pow_succ]
      change root*(root^k*wordValue e f s.1)=_
      ring
    · change wordValue e f (if y.testBit (j+k) then mid.2 ^^^ mid.1 else mid.2) = _
      rw [Finset.sum_range_succ,add_mul,← add_assoc,← h₂]
      cases h : y.testBit (j+k) <;> simp [h,wordValue_xor,h₁,root]

private theorem wordValue_eq_sum (e f y : ℕ) : wordValue e f y =
    ∑ i ∈ Finset.range e, if y.testBit i then AdjoinRoot.root (binaryMonicPoly e f)^i else 0 := by
  unfold wordValue binaryLowerPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [divbit_eq_test]
  cases h : y.testBit i <;> simp [← C_mul_X_pow_eq_monomial,AdjoinRoot.mk_X]

/-- Shift-and-add on words computes exact quotient multiplication. -/
theorem wordValue_wordMul (e f x y : ℕ) (he : 0 < e) :
    wordValue e f (wordMul e f x y) = wordValue e f x * wordValue e f y := by
  unfold wordMul
  rw [List.range_eq_range']
  have H := (wordMul_fold_spec e f y he (x%2^e,0) 0 e).2
  simp only [wordValue_zero,wordValue_mod,zero_add] at H
  rw [← wordValue_eq_sum] at H
  exact H.trans (mul_comm _ _)

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV

open Polynomial

/-- Canonical power-basis encoding of an element of the binary quotient. -/
noncomputable def fieldWordEquiv (e f : ℕ) : Fin (2^e) ≃ AdjoinRoot (binaryMonicPoly e f) :=
  (finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ : Fin e => (ZMod.finEquiv 2).toEquiv))).trans
    ((Equiv.arrowCongr (finCongr (binaryMonicPoly_natDegree e f)).symm (Equiv.refl (ZMod 2))).trans
      ((AdjoinRoot.powerBasisAux' (binaryMonicPoly_monic e f)).equivFun.symm.toEquiv))

private theorem wordCodeCoeff (e f : ℕ) (x : Fin (2^e)) (j : Fin (binaryMonicPoly e f).natDegree) :
    ((AdjoinRoot.powerBasisAux' (binaryMonicPoly_monic e f)).equivFun (fieldWordEquiv e f x)) j =
      ((x.val / 2^j.val % 2 : ℕ) : ZMod 2) := by
  unfold fieldWordEquiv
  simp only [Equiv.trans_apply, LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply]
  change (ZMod.finEquiv 2) ⟨x.val / 2^j.val % 2, _⟩ = _
  apply ZMod.val_injective 2
  change x.val / 2^j.val % 2 = _
  rw [ZMod.val_natCast, Nat.mod_mod]

/-- The power-basis equivalence picks exactly the quotient of the low bit polynomial. -/
theorem fieldWordEquiv_eq_wordValue (e f : ℕ) (x : Fin (2^e)) :
    fieldWordEquiv e f x = wordValue e f x.val := by
  apply (AdjoinRoot.powerBasisAux' (binaryMonicPoly_monic e f)).equivFun.injective
  funext j
  rw [wordCodeCoeff, Module.Basis.equivFun_apply]
  let p := binaryMonicPoly e f
  let h := binaryMonicPoly_monic e f
  have hj : j.val < e := by simpa only [binaryMonicPoly_natDegree] using j.isLt
  have hdegree : (binaryLowerPoly e x.val).degree < p.degree := by
    rw [degree_eq_natDegree h.ne_zero, binaryMonicPoly_natDegree]
    exact binaryLower_degree_lt _ _
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,wordValue,AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff h).mpr hdegree, coeff_binaryLower,if_pos hj]

/-- Multiplication in the quotient takes the canonical binary code from the executable word. -/
theorem fieldWordEquiv_wordMul (e f : ℕ) (he : 0 < e) (x y : Fin (2^e)) :
    fieldWordEquiv e f ⟨wordMul e f x.val y.val, wordMul_lt ..⟩ =
      fieldWordEquiv e f x * fieldWordEquiv e f y := by
  simp only [fieldWordEquiv_eq_wordValue]
  exact wordValue_wordMul _ _ _ _ he

/-- Binary word value `1` represents the unit, in each positive degree. -/
theorem binaryLowerPoly_one (e : ℕ) (he : 0 < e) : binaryLowerPoly e 1 = 1 := by
  ext i
  cases i with
  | zero => simp [coeff_binaryLower, he]
  | succ i =>
    have hh : 1 < (2:ℕ)^(i+1) := Nat.one_lt_two_pow (by omega)
    simp [coeff_binaryLower, Nat.div_eq_of_lt hh, coeff_one]

@[simp] theorem wordValue_one (e f : ℕ) (he : 0 < e) : wordValue e f 1 = 1 := by
  simp [wordValue, binaryLowerPoly_one _ he]

@[simp] theorem fieldWordEquiv_zero (e f : ℕ) :
    fieldWordEquiv e f ⟨0,Nat.two_pow_pos e⟩ = 0 := by simp [fieldWordEquiv_eq_wordValue]

@[simp] theorem fieldWordEquiv_one (e f : ℕ) (he : 0 < e) :
    fieldWordEquiv e f ⟨1,Nat.one_lt_two_pow he.ne'⟩ = 1 := by simp [fieldWordEquiv_eq_wordValue,he]

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev WordMulInput := ℕ × ℕ × ℕ × ℕ
abbrev encWordMulInput : WordMulInput ↪ List Bool :=
  encPair encUnary (encPair encNat (encPair encNat encNat))

private theorem xor_poly {α : Type} {enc : α ↪ List Bool} {x y : α → ℕ}
    (hx : ComputableTidilyInPolyTime x enc encNat) (hy : ComputableTidilyInPolyTime y enc encNat) :
    ComputableTidilyInPolyTime (fun p => x p ^^^ y p) enc encNat :=
  (ComputableInPolyTime.binary_xor.comp (hx.computableInPolyTime.prod hy.computableInPolyTime)).tidy

private theorem wordMulX_poly {α : Type} {enc : α ↪ List Bool} {e f x : α → ℕ}
    (he : ComputableTidilyInPolyTime e enc encUnary) (hf : ComputableTidilyInPolyTime f enc encNat)
    (hx : ComputableTidilyInPolyTime x enc encNat) :
    ComputableTidilyInPolyTime (fun p => wordMulX (e p) (f p) (x p)) enc encNat := by
  have hm := binary_two_pow.comp he
  exact xor_poly (binary_mod' (binary_mul' (const 2) hx) hm)
    ((binary_testBit hx (unary_sub.comp (he.prod (const 1)))).cond (binary_mod' hf hm) (const 0))

private abbrev WordMulState := ℕ × ℕ × ℕ
private abbrev encWordMulState : WordMulState ↪ List Bool := encPair encUnary (encPair encNat encNat)
private def wordMulIter (p : WordMulInput) (s : WordMulState) : WordMulState :=
  (s.1+1, wordMulStep p.1 p.2.1 p.2.2.2 s.1 s.2)

private theorem wordMulIter_correct (p : WordMulInput) (b j : ℕ) (s : ℕ × ℕ) :
    (wordMulIter p)^[j] (b,s) =
      (b+j,(List.range' b j).foldl (fun t i => wordMulStep p.1 p.2.1 p.2.2.2 i t) s) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,List.range'_concat,List.foldl_append]
    simp [wordMulIter,Nat.add_assoc]

/-- Multiplication of arbitrary binary words modulo an e-bit monic polynomial is
polynomial in the unary width and in the lengths of all word operands. -/
theorem wordMul_polytime : ComputableTidilyInPolyTime
    (fun p : WordMulInput => wordMul p.1 p.2.1 p.2.2.1 p.2.2.2) encWordMulInput encNat := by
  have he := fst encUnary (encPair encNat (encPair encNat encNat))
  have hargs := snd encUnary (encPair encNat (encPair encNat encNat))
  have hx := (fst encNat encNat).comp ((snd encNat (encPair encNat encNat)).comp hargs)
  let init : WordMulInput → WordMulState := fun p => (0,p.2.2.1%2^p.1,0)
  have hinit : ComputableTidilyInPolyTime init encWordMulInput encWordMulState :=
    (const 0).prod ((binary_mod' hx (binary_two_pow.comp he)).prod (const 0))
  have hstep : ComputableTidilyInPolyTime (fun p : WordMulInput × WordMulState => wordMulIter p.1 p.2)
      (encPair encWordMulInput encWordMulState) encWordMulState := by
    have hp := fst encWordMulInput encWordMulState
    have hs := snd encWordMulInput encWordMulState
    have hidx := (fst encUnary (encPair encNat encNat)).comp hs
    have hpw := (fst encNat encNat).comp ((snd encUnary (encPair encNat encNat)).comp hs)
    have ha := (snd encNat encNat).comp ((snd encUnary (encPair encNat encNat)).comp hs)
    have hf := (fst encNat (encPair encNat encNat)).comp (hargs.comp hp)
    have hy := (snd encNat encNat).comp ((snd encNat (encPair encNat encNat)).comp (hargs.comp hp))
    have hnext := wordMulX_poly (he.comp hp) hf hpw
    have hbit := (binary_testBit hy hidx).cond (xor_poly ha hpw) ha
    exact (unary_add.comp (hidx.prod (const 1))).prod (hnext.prod hbit)
  have hstate : ComputableTidilyInPolyTime (fun p : WordMulInput => (wordMulIter p)^[p.1] (init p))
      encWordMulInput encWordMulState := by
    apply iterateWithInput_of_bounded_growth he hinit hstep
    -- State lengths need not grow monotonically when the input residue is clipped.
    refine ⟨(he.polyBounded.mul (PolyBounded.const 3)).add (PolyBounded.const 5), ?_⟩
    intro p s
    simp only [wordMulIter, encWordMulState, length_encPair, encUnary_apply, List.length_replicate,
      encNat_apply, wordMulStep]
    have hSt := Nat.size_le.mpr (wordMulX_lt p.1 p.2.1 s.2.1)
    have hxor : (s.2.2 ^^^ s.2.1).size ≤ max s.2.2.size s.2.1.size := by
      apply Nat.size_le.mpr
      exact Nat.xor_lt_two_pow (Nat.size_le.mp (Nat.le_max_left ..)) (Nat.size_le.mp (Nat.le_max_right ..))
    by_cases h : p.2.2.2.testBit s.1
    · simp [h]
      simp only [Nat.size_eq_bits_len]
      have hh : max s.2.2.size s.2.1.size ≤ s.2.2.size+s.2.1.size := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
      omega
    · simp [h]
      simp only [Nat.size_eq_bits_len]
      omega
  have hres := (snd encNat encNat).comp ((snd encUnary (encPair encNat encNat)).comp hstate)
  convert hres using 1
  funext p
  simp [init,wordMulIter_correct,wordMul,List.range_eq_range']

/-- Run the coded multiplication on calculated inputs. -/
theorem wordMul_polytime' {α : Type} {enc : α ↪ List Bool} {e f x y : α → ℕ}
    (he : ComputableTidilyInPolyTime e enc encUnary) (hf : ComputableTidilyInPolyTime f enc encNat)
    (hx : ComputableTidilyInPolyTime x enc encNat) (hy : ComputableTidilyInPolyTime y enc encNat) :
    ComputableTidilyInPolyTime (fun p => wordMul (e p) (f p) (x p) (y p)) enc encNat :=
  wordMul_polytime.comp (he.prod (hf.prod (hx.prod hy)))

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV

open Polynomial Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

private theorem binaryMonicPoly_eq_with_top {e x : ℕ} (hx : x < 2^e) :
    binaryLowerPoly (e+1) (2^e+x) = binaryMonicPoly e x := by
  ext i
  unfold binaryMonicPoly
  rw [coeff_add]
  by_cases hi : i < e
  · have hb := Nat.testBit_two_pow_add_gt hi x
    simp [coeff_binaryLower,hi,show i < e+1 by omega,coeff_X_pow,show i ≠ e by omega,
      ← Nat.toNat_testBit,hb]
  · by_cases he : i = e
    · subst i
      simp [coeff_binaryLower, coeff_X_pow, Nat.div_eq_of_lt hx]
    · simp [coeff_binaryLower,hi,show ¬ i < e+1 by omega,coeff_X_pow,he]

private theorem eq_of_quotient_eq_of_small {f p q : (ZMod 2)[X]}
    (hf : f.Monic) (hp : p.degree < f.degree) (hq : q.degree < f.degree)
    (he : AdjoinRoot.mk f p = AdjoinRoot.mk f q) : p=q := by
  have he' := congrArg (AdjoinRoot.modByMonicHom hf) he
  simp only [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).mpr hp,
    (modByMonic_eq_self_iff hf).mpr hq] at he'
  exact he'

private theorem factor_test_eq {e x d u v : ℕ} (hd : d ≤ e) (hx : x < 2^e)
    (hu : u < 2^d) (hv : v < 2^(e-d)) :
    wordMul (e+1) 0 (2^d+u) (2^(e-d)+v) = 2^e+x ↔
      binaryMonicPoly e x = binaryMonicPoly d u * binaryMonicPoly (e-d) v := by
  let m := e+1
  let f := binaryMonicPoly m 0
  have hf : f.Monic := binaryMonicPoly_monic ..
  have hdf : f.degree = ↑m := by
    rw [degree_eq_natDegree hf.ne_zero]
    exact_mod_cast binaryMonicPoly_natDegree m 0
  have hleft : (binaryMonicPoly e x).degree < f.degree := by
    rw [hdf,degree_eq_natDegree (binaryMonicPoly_monic e x).ne_zero,binaryMonicPoly_natDegree]
    exact_mod_cast Nat.lt_succ_self e
  have hright : (binaryMonicPoly d u * binaryMonicPoly (e-d) v).degree < f.degree := by
    let h₁ := binaryMonicPoly_monic d u
    let h₂ := binaryMonicPoly_monic (e-d) v
    rw [hdf,degree_eq_natDegree (h₁.mul h₂).ne_zero,h₁.natDegree_mul h₂,
      binaryMonicPoly_natDegree,binaryMonicPoly_natDegree,show d+(e-d)=e by omega]
    exact_mod_cast Nat.lt_succ_self e
  have hU : binaryLowerPoly m (2^d+u) = binaryMonicPoly d u := by
    ext i
    have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff i) (binaryMonicPoly_eq_with_top hu)
    by_cases hi : i < d+1
    · simpa [coeff_binaryLower,hi,show i < m by dsimp [m]; omega] using hh
    · have hlt : 2^d+u < 2^(d+1) := by rw [pow_succ]; omega
      have hb : (2^d+u).testBit i = false := Nat.testBit_lt_two_pow (hlt.trans_le
        (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [coeff_binaryLower,hi,← Nat.toNat_testBit,hb] at hh ⊢
      exact hh
  have hV : binaryLowerPoly m (2^(e-d)+v) = binaryMonicPoly (e-d) v := by
    ext i
    have hh := congrArg (fun p : (ZMod 2)[X] => p.coeff i) (binaryMonicPoly_eq_with_top hv)
    by_cases hi : i < e-d+1
    · simpa [coeff_binaryLower,hi,show i < m by dsimp [m]; omega] using hh
    · have hlt : 2^(e-d)+v < 2^(e-d+1) := by rw [pow_succ]; omega
      have hb : (2^(e-d)+v).testBit i = false := Nat.testBit_lt_two_pow (hlt.trans_le
        (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [coeff_binaryLower,hi,← Nat.toNat_testBit,hb] at hh ⊢
      exact hh
  have ha := wordValue_wordMul m 0 (2^d+u) (2^(e-d)+v) (by omega)
  change AdjoinRoot.mk f (binaryLowerPoly m (wordMul m 0 (2^d+u) (2^(e-d)+v))) = _ at ha
  rw [show wordValue m 0 (2^d+u) = AdjoinRoot.mk f (binaryLowerPoly m (2^d+u)) by rfl,
    show wordValue m 0 (2^(e-d)+v) = AdjoinRoot.mk f (binaryLowerPoly m (2^(e-d)+v)) by rfl, hU,hV,← map_mul] at ha
  have hx' := binaryMonicPoly_eq_with_top hx
  constructor
  · intro h
    rw [h] at ha
    rw [show binaryLowerPoly m (2^e+x) = binaryMonicPoly e x from hx'] at ha
    exact eq_of_quotient_eq_of_small hf hleft hright ha
  · intro h
    have hw : wordMul m 0 (2^d+u) (2^(e-d)+v) < 2^m := wordMul_lt ..
    have hsmall : 2^e+x < 2^m := by dsimp [m]; rw [pow_succ]; omega
    let lhs : Fin (2^m) := ⟨wordMul m 0 (2^d+u) (2^(e-d)+v),hw⟩
    let rhs : Fin (2^m) := ⟨2^e+x,hsmall⟩
    have H : fieldWordEquiv m 0 lhs = fieldWordEquiv m 0 rhs := by
      rw [fieldWordEquiv_eq_wordValue,fieldWordEquiv_eq_wordValue]
      change AdjoinRoot.mk f (binaryLowerPoly m (wordMul m 0 (2^d+u) (2^(e-d)+v))) =
        AdjoinRoot.mk f (binaryLowerPoly m (2^e+x))
      rw [ha,show binaryLowerPoly m (2^e+x)=binaryMonicPoly e x from hx',h]
    exact congrArg Fin.val ((fieldWordEquiv m 0).injective H)

/-- Test a candidate for all proper factor-degree splits. The single index `uv` encodes
both lower parts as `u + 2^d*v`, so each split needs exactly `2^e` tests. -/
def modulusCheck (e x : ℕ) : Bool :=
  (List.range e).all fun d => d == 0 || (List.range (2^e)).all fun uv =>
    !(wordMul (e+1) 0 (2^d+uv%2^d) (2^(e-d)+uv/2^d) == 2^e+x)

/-- Search the entire finite monic degree-`e` slice of binary polynomials. -/
def findModulus (e : ℕ) : ℕ := ((List.range (2^e)).find? (modulusCheck e)).getD 0

theorem modulusCheck_correct {e x : ℕ} (he : 0 < e) (hx : x < 2^e) :
    modulusCheck e x = true ↔ Irreducible (binaryMonicPoly e x) := by
  rw [binaryMonicPoly_irreducible_iff_no_factor he]
  constructor
  · intro h d hd hde u v hh
    have heq : wordMul (e+1) 0 (2^d+u.val) (2^(e-d)+v.val) = 2^e+x :=
      (factor_test_eq hde.le hx u.isLt v.isLt).mpr hh
    have hp := List.all_eq_true.mp h d (List.mem_range.mpr hde)
    have hD : d ≠ 0 := by omega
    have hbd : (d == 0) = false := beq_eq_false_iff_ne.mpr hD
    change ((d == 0) || (List.range (2^e)).all fun uv =>
      !(wordMul (e+1) 0 (2^d+uv%2^d) (2^(e-d)+uv/2^d) == 2^e+x)) = true at hp
    simp only [hbd, Bool.false_or] at hp
    let uv := u.val + 2^d*v.val
    have huv : uv < 2^e := by
      have hm : (2:ℕ)^d * 2^(e-d) = 2^e := by rw [← pow_add,show d+(e-d)=e by omega]
      have hv : v.val+1 ≤ 2^(e-d) := v.isLt
      have hmul := Nat.mul_le_mul_left (2^d) hv
      dsimp [uv]
      rw [Nat.mul_add,Nat.mul_one,hm] at hmul
      omega
    have hU : uv % 2^d = u.val := by dsimp [uv]; rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt u.isLt]
    have hV : uv / 2^d = v.val := by dsimp [uv]; rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt u.isLt,Nat.zero_add]
    have hn := List.all_eq_true.mp hp uv (List.mem_range.mpr huv)
    simp [hU,hV,heq] at hn
  · intro h
    unfold modulusCheck
    apply List.all_eq_true.mpr
    intro d hd
    have hde := List.mem_range.mp hd
    by_cases hz : d=0
    · simp [hz]
    · have hbd : (d == 0) = false := beq_eq_false_iff_ne.mpr hz
      change ((d == 0) || (List.range (2^e)).all fun uv =>
        !(wordMul (e+1) 0 (2^d+uv%2^d) (2^(e-d)+uv/2^d) == 2^e+x)) = true
      simp only [hbd, Bool.false_or]
      apply List.all_eq_true.mpr
      intro uv huv
      have hUV := List.mem_range.mp huv
      have hdv : uv / 2^d < 2^(e-d) := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
        rw [← pow_add, Nat.sub_add_cancel hde.le]
        exact hUV
      let u : Fin (2^d) := ⟨uv % 2^d, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let v : Fin (2^(e-d)) := ⟨uv / 2^d, hdv⟩
      change (!(wordMul (e+1) 0 (2^d+uv%2^d) (2^(e-d)+uv/2^d) == 2^e+x)) = true
      have hne : wordMul (e+1) 0 (2^d+uv%2^d) (2^(e-d)+uv/2^d) ≠ 2^e+x := by
        intro hmul
        exact h d (by omega) hde u v ((factor_test_eq hde.le hx u.isLt v.isLt).mp hmul)
      rw [beq_eq_false_iff_ne.mpr hne]
      rfl

/-- For every positive width the search returns a valid irreducible modulus. -/
theorem findModulus_correct (e : ℕ) (he : 0 < e) :
    findModulus e < 2^e ∧ Irreducible (binaryMonicPoly e (findModulus e)) := by
  obtain ⟨x, hx⟩ := exists_binaryMonicPoly_irreducible e he
  have hsome := List.find?_isSome.mpr ⟨x.val,List.mem_range.mpr x.isLt,
    (modulusCheck_correct he x.isLt).mpr hx⟩
  cases h : (List.range (2^e)).find? (modulusCheck e) with
  | none => simp [h] at hsome
  | some y =>
    have hy := List.mem_range.mp (List.mem_of_find?_eq_some h)
    simpa [findModulus,h] using And.intro hy ((modulusCheck_correct he hy).mp (List.find?_some h))


/-- The exhaustive test is polynomial on any input encoding for which both the
width and the number of lower coefficient vectors are available as unary counters. -/
theorem findModulus_polytime {α : Type} {enc : α ↪ List Bool} {width : α → ℕ}
    (hw : ComputableTidilyInPolyTime width enc encUnary)
    (hr : ComputableTidilyInPolyTime (fun x => 2^(width x)) enc encUnary) :
    ComputableTidilyInPolyTime (fun x => findModulus (width x)) enc encNat := by
  let encCandidate : α × ℕ ↪ List Bool := encPair enc encUnary
  let encSplit : (α × ℕ) × ℕ ↪ List Bool := encPair encCandidate encUnary
  let encFactor : ((α × ℕ) × ℕ) × ℕ ↪ List Bool := encPair encSplit encUnary
  have hCandidateInput := fst enc encUnary
  have hSplitCandidate := fst encCandidate encUnary
  have hSplitInput := hCandidateInput.comp hSplitCandidate
  have hSplitDegree := snd encCandidate encUnary
  have hFactorSplit := fst encSplit encUnary
  have hFactorCandidate := hSplitCandidate.comp hFactorSplit
  have hWidth := hw.comp (hSplitInput.comp hFactorSplit)
  have hDegree := hSplitDegree.comp hFactorSplit
  have hCandidate := unary_to_binary.comp ((snd enc encUnary).comp hFactorCandidate)
  have hIndex := unary_to_binary.comp (snd encSplit encUnary)
  have hHalf := binary_two_pow.comp hDegree
  have hOtherHalf := binary_two_pow.comp (unary_sub.comp (hWidth.prod hDegree))
  have hLeft := binary_add' hHalf (binary_mod' hIndex hHalf)
  have hRight := binary_add' hOtherHalf (binary_div' hIndex hHalf)
  have hProduct := wordMul_polytime' (unary_add.comp (hWidth.prod (const 1))) (const 0) hLeft hRight
  have hTarget := binary_add' (binary_two_pow.comp hWidth) hCandidate
  have hFactorTest : ComputableTidilyInPolyTime
      (fun p : ((α × ℕ) × ℕ) × ℕ =>
        !(wordMul (width p.1.1.1+1) 0 (2^p.1.2 + p.2 % 2^p.1.2)
          (2^(width p.1.1.1-p.1.2) + p.2 / 2^p.1.2) == 2^(width p.1.1.1) + p.1.1.2))
      encFactor encBool :=
    bool_not.comp (hProduct.beq hTarget)
  have hSplitTest : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ =>
        p.2 == 0 || (List.range (2^width p.1.1)).all fun uv =>
          !(wordMul (width p.1.1+1) 0 (2^p.2+uv%2^p.2)
            (2^(width p.1.1-p.2)+uv/2^p.2) == 2^(width p.1.1)+p.1.2))
      encSplit encBool :=
    bool_or.comp ((unary_beq hSplitDegree (const 0)).prod
      (allWithInput (range.comp (hr.comp hSplitInput)) hFactorTest))
  have hCheck : ComputableTidilyInPolyTime (fun p : α × ℕ => modulusCheck (width p.1) p.2)
      encCandidate encBool :=
    allWithInput (range.comp (hw.comp hCandidateInput)) hSplitTest
  exact unary_to_binary.comp (optionGetDWithInput (findWithInput (range.comp hr) hCheck) (const 0))

end TimeSpaceMA.GUV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open TimeSpaceMA.GUV.BinaryFieldArithmetic (radix radix_pos clip clip_bound clip_eq word word_val)
open scoped BigOperators

namespace TimeSpaceMA.GUV

variable (a : ℕ) (mul : FieldBinInput → ℕ)

def generatorOrder (a n : ℕ) := 2^halfSeed a n - 1

theorem fieldWidth_poly {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => 2*halfSeed a (n x)) enc encUnary := by
  exact unary_mul.comp ((const 2).prod (BinaryFieldArithmetic.native_halfSeed a hn))

private theorem radix_poly {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => radix a (n x)) enc encNat :=
  binary_two_pow.comp (fieldWidth_poly a hn)

theorem radix_count_poly {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => radix a (n x)) enc encUnary := by
  refine binary_to_unary_bounded (radix_poly a hn)
    ((unary_pow (2*a)).comp (unary_mul.comp ((const 2).prod (unary_add.comp (hn.prod (const 1)))))) ?_
  intro x
  have hbase : (2 : ℕ)^(max 1 (n x)).size ≤ 2*(n x + 1) := by
    cases he : (max 1 (n x)).size with
    | zero => rw [pow_zero]; omega
    | succ m =>
      have hpow : (2:ℕ)^m ≤ max 1 (n x) := Nat.lt_size.mp (by omega)
      rw [pow_succ]
      omega
  change 2^(2*halfSeed a (n x)) ≤ (2*(n x+1))^(2*a)
  rw [halfSeed, ← Nat.mul_assoc, Nat.mul_comm (2*a), pow_mul]
  exact Nat.pow_le_pow_left hbase _

private theorem generatorOrder_poly {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => generatorOrder a (n x)) enc encUnary := by
  let c := BinaryFieldArithmetic.native_halfSeed a hn
  refine binary_to_unary_bounded
    (binary_sub' (binary_two_pow.comp c) (const 1)) (radix_count_poly a hn) ?_
  intro x
  exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

private theorem poly_eq {α : Type} {enc : α ↪ List Bool} {x y : α → ℕ}
    (hx : ComputableTidilyInPolyTime x enc encNat) (hy : ComputableTidilyInPolyTime y enc encNat) :
    ComputableTidilyInPolyTime (fun p => decide (x p = y p)) enc encBool := by
  have h := (binary_le' hx hy).ite_decide (binary_le' hy hx) (const false)
  apply h.of_enc_eq
  intro p
  by_cases he : x p ≤ y p
  · by_cases he' : y p ≤ x p
    · simp [le_antisymm he he']
    · have hne : x p ≠ y p := fun H => he' H.ge
      simp [he, he', hne]
  · have hne : x p ≠ y p := fun H => he H.le
    simp [he, hne]

abbrev OrderInput := ℕ × ℕ
abbrev encOrderInput : OrderInput ↪ List Bool := encPair encUnary encNat

abbrev OrderState := ℕ × Bool
abbrev encOrderState : OrderState ↪ List Bool := encPair encNat encBool

def oneCheck (p : OrderInput) (s : OrderState) : OrderState :=
  let (n,y) := p
  let (w,clean) := s
  (clip a n (mul (n,w,clip a n y)), clean && (w != 1))

def orderTrace (p : OrderInput) (j : ℕ) : OrderState :=
  (oneCheck a mul p)^[j] (clip a p.1 (mul (p.1,1,clip a p.1 p.2)), true)

theorem orderTrace_succ (p : OrderInput) (j : ℕ) :
    orderTrace a mul p (j+1) = oneCheck a mul p (orderTrace a mul p j) := by
  simp [orderTrace, Function.iterate_succ_apply']

theorem orderTrace_radix (p : OrderInput) (j : ℕ) : (orderTrace a mul p j).1 < radix a p.1 := by
  cases j with
  | zero => exact clip_bound ..
  | succ j => rw [orderTrace_succ]; exact clip_bound ..

/-- Test the desired order using the powers x,x²,...,xᴰ. -/
def isGenerator (p : OrderInput) : Bool :=
  let d := generatorOrder a p.1
  let (w,clean) := orderTrace a mul p (d-1)
  (w == 1) && clean

private theorem oneCheck_poly
    (hmul : ComputableInPolyTime mul encFieldBinInput encNat) :
    ComputableTidilyInPolyTime (fun p : OrderInput × OrderState => oneCheck a mul p.1 p.2)
      (encPair encOrderInput encOrderState) encOrderState := by
  let hp := fst encOrderInput encOrderState
  let hstate := snd encOrderInput encOrderState
  let hn := hp.fst'
  let hy := binary_mod' hp.snd' (radix_poly a hn)
  let hm := binary_mod' (hmul.tidy.comp (hn.prod (hstate.fst'.prod hy))) (radix_poly a hn)
  have hclean : ComputableTidilyInPolyTime
      (fun p : OrderInput × OrderState => p.2.2 && (p.2.1 != 1))
      (encPair encOrderInput encOrderState) encBool := by
    have hb : ComputableTidilyInPolyTime (fun p : OrderInput × OrderState => decide (p.2.2 = true))
        (encPair encOrderInput encOrderState) encBool := by simpa using hstate.snd'
    apply (hb.ite_decide ((poly_eq hstate.fst' (const 1)).ite_decide (const (encMid := encBool) false) (const true))
      (const false)).of_enc_eq
    intro p
    by_cases hc : p.2.2 <;> by_cases he : p.2.1 = 1 <;> simp [hc, he]
  exact hm.prod hclean

theorem isGenerator_polytime
    (hmul : ComputableInPolyTime mul encFieldBinInput encNat) :
    ComputableTidilyInPolyTime (isGenerator a mul) encOrderInput encBool := by
  let hn := fst encUnary encNat
  let hy := snd encUnary encNat
  let hcount := unary_sub.comp ((generatorOrder_poly a hn).prod (const 1))
  have hinit : ComputableTidilyInPolyTime (fun p : OrderInput => orderTrace a mul p 0)
      encOrderInput encOrderState := (binary_mod' (hmul.tidy.comp (hn.prod ((const 1).prod
    (binary_mod' hy (radix_poly a hn))))) (radix_poly a hn)).prod (const true)
  let size (p : OrderInput) := 4*halfSeed a p.1+2
  have hm := (fieldWidth_poly a hn).polyBounded
  have hsize : PolyBounded (fun p : OrderInput => (encOrderInput p).length) size := by
    apply ((hm.add hm).add (.const 2)).mono
    intro p
    dsimp [size]
    omega
  have hst : ∀ (p : OrderInput) (i : ℕ), i ≤ generatorOrder a p.1-1 →
      (encOrderState (orderTrace a mul p i)).length ≤ size p := by
    intro p i _
    have hw := Nat.size_le.mpr (orderTrace_radix a mul p i)
    simp only [encOrderState, length_encPair, encNat_apply, Nat.size_eq_bits_len, encBool_apply,
      List.length_singleton]
    dsimp [size]
    omega
  have hrun : ComputableTidilyInPolyTime (fun p : OrderInput =>
      orderTrace a mul p (generatorOrder a p.1-1)) encOrderInput encOrderState :=
    iterateWith id' hcount hinit (oneCheck_poly a mul hmul) hsize hst
  apply ((poly_eq hrun.fst' (const 1)).ite_decide hrun.snd' (const false)).of_enc_eq
  intro p
  by_cases he : (orderTrace a mul p (generatorOrder a p.1-1)).1 = 1 <;> simp [isGenerator, he]

theorem isGenerator_correct {F : Type} [Field F] (n : ℕ)
    (code : FieldWord a n ≃ F) (hD : 0 < generatorOrder a n)
    (hOne : code (word a n 1) = 1)
    (hmul : ∀ x y : FieldWord a n,
      clip a n (mul (n,x.val,y.val)) = (code.symm (code x * code y)).val)
    (y : FieldWord a n) :
    isGenerator a mul (n,y.val) = true ↔ orderOf (code y) = generatorOrder a n := by
  let d := generatorOrder a n
  let p : OrderInput := (n,y.val)
  have hny : y.val < radix a n := y.isLt
  have hneq : 1 < radix a n := by
    have hh : 1 < 2^halfSeed a n := by unfold generatorOrder at hD; omega
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have heq : word a n y.val = y := Fin.ext (word_val _ _ _ hny)
  have h1 (w : ℕ) (hw : w < radix a n) : code (word a n w) = 1 ↔ w = 1 := by
    rw [← hOne, code.injective.eq_iff, Fin.ext_iff, word_val _ _ _ hw, word_val _ _ _ hneq]
  have hmul' (x : ℕ) (hx : x < radix a n) :
      code (word a n (clip a n (mul (n,x,clip a n y.val)))) =
        code (word a n x) * code y := by
    have hh := hmul (word a n x) y
    rw [word_val _ _ _ hx] at hh
    apply code.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Fin.ext
    rw [word_val _ _ _ (clip_bound ..), clip_eq _ _ _ hny]
    exact hh
  have htrace (j : ℕ) :
      code (word a n (orderTrace a mul p j).1) = (code y)^(j+1) ∧
        ((orderTrace a mul p j).2 = true ↔ ∀ i < j, (code y)^(i+1) ≠ 1) := by
    induction j with
    | zero =>
      change code (word a n (clip a n (mul (n,1,clip a n y.val)))) = (code y)^1 ∧ _
      rw [hmul' 1 hneq, hOne, one_mul, pow_one]
      simp [orderTrace]
    | succ j ih =>
      let w := (orderTrace a mul p j).1
      have hw : w < radix a n := orderTrace_radix a mul p j
      rw [orderTrace_succ]
      change code (word a n (clip a n (mul (n,w,clip a n y.val)))) = (code y)^(j+1+1) ∧
        (((orderTrace a mul p j).2 && (w != 1)) = true ↔ ∀ i < j+1, _)
      refine ⟨by rw [hmul' w hw, ih.1, pow_succ (code y) (j+1)], ?_⟩
      have hne : (w != 1) = true ↔ (code y)^(j+1) ≠ 1 := by
        rw [← ih.1]
        change _ ↔ code (word a n w) ≠ 1
        rw [ne_eq, h1 w hw]
        simp
      rw [Bool.and_eq_true, ih.2, hne]
      constructor
      · rintro ⟨hbefore, hlast⟩ i hi
        by_cases h : i = j
        · rwa [h]
        · exact hbefore i (by omega)
      · intro h
        exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  obtain ⟨hw, hc⟩ := htrace (d-1)
  have hs : d-1+1 = d := by omega
  have hfinish : (orderTrace a mul p (d-1)).1 = 1 ↔ (code y)^d = 1 := by
    rw [← h1 _ (orderTrace_radix a mul p _), hw, hs]
  change (((orderTrace a mul p (d-1)).1 == 1) && (orderTrace a mul p (d-1)).2) = true ↔ _
  rw [Bool.and_eq_true, beq_iff_eq, hfinish, hc, orderOf_eq_iff hD]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h j hj hjp
    have he : j-1+1 = j := by omega
    exact he ▸ h (j-1) (by omega)
  · intro h i hi
    exact h (i+1) (by omega) (by omega)

abbrev SearchState := ℕ × ℕ × Bool
abbrev encSearchState : SearchState ↪ List Bool := encPair encUnary (encPair encNat encBool)

def searchStep (n : ℕ) (s : SearchState) : SearchState :=
  if s.2.2 then (s.1+1,s.2.1,true)
  else if isGenerator a mul (n,s.1) then (s.1+1,s.1,true) else (s.1+1,0,false)

def searchTrace (n i : ℕ) : SearchState :=
  (searchStep a mul n)^[i] (0,0,false)

def primitiveCode (n : ℕ) : ℕ :=
  (searchTrace a mul n (radix a n)).2.1

theorem searchTrace_bounds (n i : ℕ) :
    let s := searchTrace a mul n i
    s.1 = i ∧ (if s.2.2 then s.2.1 < i ∧ isGenerator a mul (n,s.2.1) = true
       else s.2.1 = 0 ∧ ∀ j < i, isGenerator a mul (n,j) = false) := by
  induction i with
  | zero => simp [searchTrace]
  | succ i ih =>
    let s := searchTrace a mul n i
    change s.1 = i ∧ _ at ih
    have h := ih.1
    have heq : searchTrace a mul n (i+1) = searchStep a mul n s := by
      simp only [searchTrace, s, Function.iterate_succ_apply']
    rw [heq]
    unfold searchStep
    by_cases hs : s.2.2 = true
    · have hh := ih.2
      change (if s.2.2 then _ else _) at hh
      simp only [hs, if_true] at hh
      simpa only [h, hs, if_true] using
        (show i+1 = i+1 ∧ _ from ⟨rfl, (hh.1.trans (Nat.lt_succ_self i)), hh.2⟩)
    · have hh := ih.2
      change (if s.2.2 then _ else _) at hh
      simp only [hs] at hh
      by_cases he : isGenerator a mul (n,i) = true
      · simp [hs, h, he]
      · simp only [hs, if_false, h, he, true_and, Bool.false_eq_true]
        intro j hj
        by_cases hj' : j = i
        · subst j; cases hE : isGenerator a mul (n,i) <;> simp_all
        · exact hh.2 j (by omega)

theorem primitiveCode_correct_of_exists (n : ℕ)
    (he : ∃ y < radix a n, isGenerator a mul (n,y) = true) :
    primitiveCode a mul n < radix a n ∧ isGenerator a mul (n,primitiveCode a mul n) = true := by
  let s := searchTrace a mul n (radix a n)
  have hs := (searchTrace_bounds a mul n (radix a n)).2
  change (if s.2.2 then _ else _) at hs
  by_cases hb : s.2.2 = true
  · simpa only [primitiveCode, s, hb, if_true] using hs
  · obtain ⟨y, hy, h⟩ := he
    simp only [hb] at hs
    rw [hs.2 y hy] at h
    contradiction

theorem primitiveCode_bound (n : ℕ) : primitiveCode a mul n < radix a n := by
  have hs := (searchTrace_bounds a mul n (radix a n)).2
  split at hs
  · exact hs.1
  · show (searchTrace a mul n (radix a n)).2.1 < _
    rw [hs.1]
    exact radix_pos _ _

private theorem searchStep_polytime
    (hmul : ComputableInPolyTime mul encFieldBinInput encNat) :
    ComputableTidilyInPolyTime (fun p : ℕ × SearchState => searchStep a mul p.1 p.2)
      (encPair encUnary encSearchState) encSearchState := by
  let hn := fst encUnary encSearchState
  let hs := snd encUnary encSearchState
  let hi := hs.fst'
  let hval := hs.snd'.fst'
  let hnext := unary_add.comp (hi.prod (const 1))
  have hb : ComputableTidilyInPolyTime (fun p : ℕ × SearchState => decide (p.2.2.2 = true))
      (encPair encUnary encSearchState) encBool := by simpa using hs.snd'.snd'
  have hg : ComputableTidilyInPolyTime (fun p : ℕ × SearchState =>
      decide (isGenerator a mul (p.1,p.2.1) = true))
      (encPair encUnary encSearchState) encBool := by
    have H : ComputableTidilyInPolyTime (fun p : ℕ × SearchState => isGenerator a mul (p.1,p.2.1))
        (encPair encUnary encSearchState) encBool :=
      (isGenerator_polytime a mul hmul).comp (hn.prod (unary_to_binary.comp hi))
    simpa using H
  exact hb.ite_decide (hnext.prod (hval.prod (const true))) (hg.ite_decide
    (hnext.prod ((unary_to_binary.comp hi).prod (const true))) (hnext.prod ((const 0).prod (const false))))

theorem primitiveCode_polytime
    (hmul : ComputableInPolyTime mul encFieldBinInput encNat) :
    ComputableInPolyTime (primitiveCode a mul) encUnary encNat := by
  let count := radix_count_poly a (id' (encIn := encUnary))
  let width := fieldWidth_poly a (id' (encIn := encUnary))
  let size (n : ℕ) := 2*radix a n + 2*(2*halfSeed a n) + 3
  have hp : PolyBounded (fun n : ℕ => (encUnary n).length) size := by
    apply ((count.polyBounded.add count.polyBounded).add
      (width.polyBounded.add width.polyBounded)).add (.const 3) |>.mono
    intro n
    dsimp [size]
    omega
  have hs (n i : ℕ) (hi : i ≤ radix a n) :
      (encSearchState (searchTrace a mul n i)).length ≤ size n := by
    obtain ⟨hj,hv⟩ := searchTrace_bounds a mul n i
    have hv' : (searchTrace a mul n i).2.1 < radix a n := by
      split at hv
      · exact hv.1.trans_le hi
      · rw [hv.1]
        exact radix_pos _ _
    have hw := Nat.size_le.mpr hv'
    simp only [encSearchState, length_encPair, encUnary_apply, List.length_replicate, encNat_apply,
      Nat.size_eq_bits_len, encBool_apply, List.length_singleton]
    dsimp [size]
    omega
  have H : ComputableTidilyInPolyTime (fun n => searchTrace a mul n (radix a n))
      encUnary encSearchState :=
    iterateWith id' count (const (0,0,false)) (searchStep_polytime a mul hmul) hp hs
  exact H.snd'.fst'.computableInPolyTime

theorem mem_subfield_of_order {K F : Type} [Field K] [Field F] [Fintype K]
    (φ : K →+* F) (x : F) (hx : orderOf x = Fintype.card K - 1) :
    ∃ z : K, φ z = x ∧ orderOf z = Fintype.card K - 1 := by
  classical
  let h := Fintype.card K
  have hh : 1 < h := Fintype.one_lt_card
  let P : Polynomial F := Polynomial.X^h - Polynomial.X
  have hde : P.natDegree = h := by
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    simpa only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] using hh
  have hnon : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (hde ▸ (by omega))
  let T := (Finset.univ : Finset K).image φ
  have hT₀ : T.card = h := (Finset.card_image_of_injective _ φ.injective).trans Finset.card_univ
  have hT : T ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    apply Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hnon).mpr _)
    have hfixed : (φ z)^h = φ z :=
      (map_pow φ z h).symm.trans (congrArg φ (FiniteField.pow_card z))
    simp [P, hfixed]
  have hroot : x ∈ P.roots.toFinset := by
    have hpow : x^(h-1) = 1 := hx ▸ pow_orderOf_eq_one x
    have hx' : x^h = x := by
      conv_lhs => rw [show h = h-1+1 by omega]
      rw [pow_succ, hpow, one_mul]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hnon).mpr (by simp [P, hx']))
  have heq : T = P.roots.toFinset := Finset.eq_of_subset_of_card_le hT (by
    rw [hT₀, ← hde]
    exact (Multiset.toFinset_card_le P.roots).trans P.card_roots')
  rw [← heq] at hroot
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hroot
  exact ⟨z, he, (orderOf_injective φ.toMonoidHom φ.injective z).symm.trans (he ▸ hx)⟩

theorem primitiveCode_correct {K F : Type} [Field K] [Field F] [Fintype K]
    (n : ℕ) (φ : K →+* F) (code : FieldWord a n ≃ F)
    (hK : Fintype.card K = 2^halfSeed a n)
    (hOne : code (word a n 1) = 1)
    (hmul : ∀ x y : FieldWord a n,
      clip a n (mul (n,x.val,y.val)) = (code.symm (code x * code y)).val) :
    ∃ ζ : K, orderOf ζ = 2^halfSeed a n - 1 ∧
      primitiveCode a mul n = (code.symm (φ ζ)).val := by
  have hh : 1 < Fintype.card K := Fintype.one_lt_card
  have hd : 0 < generatorOrder a n := by
    rw [generatorOrder, ← hK]
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf (φ (g : K)) = generatorOrder a n := by
    calc
      _ = orderOf (g : K) := orderOf_injective φ.toMonoidHom φ.injective (g : K)
      _ = _ := by rw [orderOf_units,
        orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
        hK, generatorOrder]
  let u := code.symm (φ (g : K))
  have htest := (isGenerator_correct a mul n code hd hOne hmul u).mpr (by simpa [u] using hord)
  obtain ⟨hbound, hsuccess⟩ := primitiveCode_correct_of_exists a mul n ⟨u.val, u.isLt, htest⟩
  let v : FieldWord a n := ⟨primitiveCode a mul n, hbound⟩
  have hs := (isGenerator_correct a mul n code hd hOne hmul v).mp hsuccess
  rw [generatorOrder, ← hK] at hs
  obtain ⟨ζ, hζ, ho⟩ := mem_subfield_of_order φ (code v) hs
  refine ⟨ζ, hK ▸ ho, ?_⟩
  rw [hζ, Equiv.symm_apply_apply]

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV

open Polynomial Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev WordField (e f : ℕ) : Type := AdjoinRoot (binaryMonicPoly e f)

theorem wordField_finrank (e f : ℕ) : Module.finrank (ZMod 2) (WordField e f) = e :=
  finrank_quotient_span_eq_natDegree.trans (binaryMonicPoly_natDegree e f)

@[instance_reducible] noncomputable def wordField_fintype (e f : ℕ) : Fintype (WordField e f) :=
  Fintype.ofEquiv _ (fieldWordEquiv e f)

noncomputable def wordField_embed (c g f : ℕ)
    (hg : Irreducible (binaryMonicPoly c g)) (hf : Irreducible (binaryMonicPoly (2*c) f)) :
    WordField c g →+* WordField (2*c) f := by
  let : Fact (Irreducible (binaryMonicPoly c g)) := ⟨hg⟩
  let : Fact (Irreducible (binaryMonicPoly (2*c) f)) := ⟨hf⟩
  let : Fintype (WordField (2*c) f) := wordField_fintype (2*c) f
  let hh : Module.finrank (ZMod 2) (WordField c g) ∣
      Module.finrank (ZMod 2) (WordField (2*c) f) := by
    rw [wordField_finrank, wordField_finrank]
    exact Nat.dvd_mul_left _ _
  exact (FiniteField.nonempty_algHom_of_finrank_dvd hh).some.toRingHom


section Assemble

open BinaryFieldArithmetic (clip clip_eq clip_bound radix word word_val)

variable (a : ℕ) (ha : 0 < a)
variable (modulus : ℕ → ℕ)
variable (hirr : ∀ n, Irreducible (binaryMonicPoly (2*halfSeed a n) (modulus n)))

private noncomputable def modulusSmall (n : ℕ) : ℕ :=
  (exists_binaryMonicPoly_irreducible (halfSeed a n) (halfSeed_pos ha n)).choose.val

include ha in
private theorem modulusSmall_irreducible (n : ℕ) :
    Irreducible (binaryMonicPoly (halfSeed a n) (modulusSmall a ha n)) :=
  (exists_binaryMonicPoly_irreducible (halfSeed a n) (halfSeed_pos ha n)).choose_spec

private abbrev CodeK (n : ℕ) := WordField (halfSeed a n) (modulusSmall a ha n)
private abbrev CodeF (n : ℕ) := WordField (2*halfSeed a n) (modulus n)

@[instance_reducible] private noncomputable def codeKField (n : ℕ) : Field (CodeK a ha n) :=
  let : Fact (Irreducible (binaryMonicPoly (halfSeed a n) (modulusSmall a ha n))) :=
    ⟨modulusSmall_irreducible a ha n⟩
  AdjoinRoot.instField

@[instance_reducible] private noncomputable def codeFField (n : ℕ) : Field (CodeF a modulus n) :=
  let : Fact (Irreducible (binaryMonicPoly (2*halfSeed a n) (modulus n))) :=
    ⟨hirr n⟩
  AdjoinRoot.instField

private noncomputable def embedWord (n : ℕ) : CodeK a ha n →+* CodeF a modulus n :=
  wordField_embed (halfSeed a n) (modulusSmall a ha n) (modulus n)
    (modulusSmall_irreducible a ha n) (hirr n)

def quotientMul : FieldBinInput → ℕ := fun (n,x,y) => wordMul (2*halfSeed a n) (modulus n) x y

private theorem quotientMul_polytime
    (hMod : ComputableInPolyTime modulus encUnary encNat)
    (hMul : ComputableTidilyInPolyTime
      (fun p : WordMulInput => wordMul p.1 p.2.1 p.2.2.1 p.2.2.2) encWordMulInput encNat) :
    ComputableInPolyTime (quotientMul a modulus) encFieldBinInput encNat := by
  let hn := fst encUnary (encPair encNat encNat)
  let tail := snd encUnary (encPair encNat encNat)
  have hw : ComputableTidilyInPolyTime
      (fun p : FieldBinInput => 2*halfSeed a p.1) encFieldBinInput encUnary := by
    exact unary_mul.comp ((const 2).prod (BinaryFieldArithmetic.native_halfSeed a hn))
  exact (hMul.comp (hw.prod ((hMod.tidy.comp hn).prod tail))).computableInPolyTime

include ha in
private theorem quotientMul_correct (n : ℕ)
    (x y : FieldWord a n) :
    let e := 2*halfSeed a n
    let E := fieldWordEquiv e (modulus n)
    clip a n (quotientMul a modulus (n,x.val,y.val)) =
      (E.symm (E x * E y)).val := by
  have hc := wordMul_lt (2*halfSeed a n) (modulus n) x.val y.val
  have he : 0 < 2*halfSeed a n := Nat.mul_pos (by decide) (halfSeed_pos ha n)
  dsimp [quotientMul]
  rw [clip_eq _ _ _ hc]
  have h := fieldWordEquiv_wordMul (2*halfSeed a n) (modulus n) he x y
  simpa only [Equiv.symm_apply_apply] using
    congrArg (fun z => ((fieldWordEquiv (2*halfSeed a n) (modulus n)).symm z).val) h

private theorem quotientAdd_correct (n : ℕ) (x y : FieldWord a n) :
    let e := 2*halfSeed a n
    let E := fieldWordEquiv e (modulus n)
    clip a n (x.val ^^^ y.val) = (E.symm (E x + E y)).val := by
  let e := 2*halfSeed a n
  let E := fieldWordEquiv e (modulus n)
  have H : E ⟨clip a n (x.val ^^^ y.val), clip_bound ..⟩ = E x + E y := by
    simp only [E, fieldWordEquiv_eq_wordValue, clip, radix, wordValue_mod, e, wordValue_xor]
  simpa only [Equiv.symm_apply_apply] using congrArg (fun x => (E.symm x).val) H

include ha in
private theorem primitive_exists (n : ℕ) :
    ∃ ζ : CodeK a ha n, orderOf ζ = 2^halfSeed a n - 1 ∧
      primitiveCode a (quotientMul a modulus) n =
        ((fieldWordEquiv (2*halfSeed a n) (modulus n)).symm
          (embedWord a ha modulus hirr n ζ)).val := by
  let : Field (CodeK a ha n) := codeKField a ha n
  let : Field (CodeF a modulus n) := codeFField a modulus hirr n
  let : Fintype (CodeK a ha n) := wordField_fintype (halfSeed a n) (modulusSmall a ha n)
  have hK : Fintype.card (CodeK a ha n) = 2^halfSeed a n :=
    (Fintype.card_congr (fieldWordEquiv (halfSeed a n) (modulusSmall a ha n)).symm).trans
      (Fintype.card_fin _)
  apply primitiveCode_correct a (quotientMul a modulus) n (embedWord a ha modulus hirr n)
    (fieldWordEquiv (2*halfSeed a n) (modulus n)) hK
  · have hp : 0 < 2*halfSeed a n := Nat.mul_pos (by decide) (halfSeed_pos ha n)
    have he : word a n 1 = ⟨1,Nat.one_lt_two_pow hp.ne'⟩ :=
      Fin.ext (word_val _ _ _ (Nat.one_lt_two_pow hp.ne'))
    rw [he]
    exact fieldWordEquiv_one _ _ hp
  · exact quotientMul_correct a ha modulus n

private theorem quotientCoeff_correct (n : ℕ) (b : Bool) :
    let c := halfSeed a n
    let E := fieldWordEquiv (2*c) (modulus n)
    let D := fieldWordEquiv c (modulusSmall a ha n)
    clip a n b.toNat = (E.symm (embedWord a ha modulus hirr n
      (D ⟨b.toNat,(show b.toNat < 2 from by cases b <;> decide).trans_le
          (Nat.le_pow (halfSeed_pos ha n))⟩))).val := by
  have hc := halfSeed_pos ha n
  have he : 0 < 2*halfSeed a n := Nat.mul_pos (by decide) hc
  dsimp
  cases b with
  | false =>
    simp only [Bool.toNat_false]
    change clip a n 0 = _
    rw [clip_eq _ _ _ (BinaryFieldArithmetic.radix_pos ..), fieldWordEquiv_zero, map_zero]
    have h := (fieldWordEquiv_zero (2*halfSeed a n) (modulus n))
    rw [← h, Equiv.symm_apply_apply]
  | true =>
    simp only [Bool.toNat_true]
    rw [clip_eq _ _ _ (Nat.one_lt_two_pow he.ne')]
    have h := fieldWordEquiv_one (halfSeed a n) (modulusSmall a ha n) hc
    have H := fieldWordEquiv_one (2*halfSeed a n) (modulus n) he
    rw [h, map_one, ← H, Equiv.symm_apply_apply]

/-- Construct the low-level arithmetic interface from one uniform modulus finder.
Primitive search, coefficient symbols, and quotient evaluation have explicit
implementations independent of the chosen algorithm for finding the moduli. -/
noncomputable def binaryFieldArithmetic_of_modulus
    (hMod : ComputableInPolyTime modulus encUnary encNat)
    (hMul : ComputableTidilyInPolyTime
      (fun p : WordMulInput => wordMul p.1 p.2.1 p.2.2.1 p.2.2.2) encWordMulInput encNat) :
    BinaryFieldArithmetic a ha where
  K := CodeK a ha
  F := CodeF a modulus
  fieldK := codeKField a ha
  fieldF := codeFField a modulus hirr
  charF n := by
    let : Field (CodeF a modulus n) := codeFField a modulus hirr n
    exact CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (CodeF a modulus n)) 2 (by decide)
  codeK n := fieldWordEquiv (halfSeed a n) (modulusSmall a ha n)
  codeF n := fieldWordEquiv (2*halfSeed a n) (modulus n)
  embed := embedWord a ha modulus hirr
  primitive n := (primitive_exists a ha modulus hirr n).choose
  primitive_order n _ := (primitive_exists a ha modulus hirr n).choose_spec.1
  add := fun (_,x,y) => x ^^^ y
  mul := quotientMul a modulus
  coeff := fun p => p.2.toNat
  zero := fun _ => 0
  generator := primitiveCode a (quotientMul a modulus)
  add_native := ComputableInPolyTime.binary_xor.comp (snd encUnary (encPair encNat encNat)).computableInPolyTime
  mul_native := quotientMul_polytime a modulus hMod hMul
  coeff_native := by
    have hBool := snd encUnary encBool
    have H : ComputableTidilyInPolyTime (fun p : FieldCoeffInput => decide (p.2 = true))
        encFieldCoeffInput encBool := by simpa using hBool
    apply (H.ite_decide (const 1) (const 0) : ComputableTidilyInPolyTime _ encFieldCoeffInput encNat)
      |>.computableInPolyTime.of_enc_eq
    intro q
    cases q.2 <;> rfl
  zero_native := (const 0 : ComputableTidilyInPolyTime _ encUnary encNat).computableInPolyTime
  generator_native := primitiveCode_polytime a (quotientMul a modulus)
    (quotientMul_polytime a modulus hMod hMul)
  add_correct n _ x y := quotientAdd_correct a modulus n x y
  mul_correct n _ x y := quotientMul_correct a ha modulus n x y
  coeff_correct n _ b := quotientCoeff_correct a ha modulus hirr n b
  zero_correct n _ := by
    change clip a n 0 = ((fieldWordEquiv _ _).symm 0).val
    rw [clip_eq _ _ _ (BinaryFieldArithmetic.radix_pos ..)]
    have h := fieldWordEquiv_zero (2*halfSeed a n) (modulus n)
    rw [← h, Equiv.symm_apply_apply]
  generator_correct n _ := by
    change clip a n (primitiveCode a (quotientMul a modulus) n) = _
    rw [clip_eq _ _ _ (primitiveCode_bound ..)]
    exact (primitive_exists a ha modulus hirr n).choose_spec.2

end Assemble

end TimeSpaceMA.GUV
open TimeSpaceMA.GUV Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

theorem solution : ∀ a (ha : 0 < a), Nonempty (BinaryFieldArithmetic a ha) := by
  intro a ha
  let m (n : ℕ) := findModulus (2*halfSeed a n)
  have hm : ∀ n, Irreducible (binaryMonicPoly (2*halfSeed a n) (m n)) :=
    fun n => (findModulus_correct _ (Nat.mul_pos (by decide) (halfSeed_pos ha n))).2
  have hmn : ComputableInPolyTime m encUnary encNat :=
    (findModulus_polytime (fieldWidth_poly a (id' (encIn := encUnary)))
      (radix_count_poly a (id' (encIn := encUnary)))).computableInPolyTime
  exact ⟨binaryFieldArithmetic_of_modulus a ha m hm hmn wordMul_polytime⟩

