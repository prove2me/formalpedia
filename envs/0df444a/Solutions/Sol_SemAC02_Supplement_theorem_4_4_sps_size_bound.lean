-- Prove2me | solution 1 for SemAC02.Supplement.theorem_4_4_sps_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T08:18:45.808644+00:00
-- url     : https://prove2.me/submissions/a3faf392-44ed-48e3-88c6-820553b86d03

import Definitions.Def_SemAC02_Supplement_ACirc
import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Theorems.Thm_SemAC02_lemma_2_1_semantic_simulation

open _root_.SemAC02 _root_.SemAC02.Supplement _root_.SemAC02.Supplement.ACirc
open _root_.AC02Frege _root_.LiftSAParity
namespace P2MSPSSizeBoundProof
section
-- Inlined Solutions.P2MArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.P2MArithmeticCircuitBasics
end

section
-- Inlined Solutions.P2MLinearFunctionalPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MLinearFunctionalPolynomials

open MvPolynomial

noncomputable def linearPoly {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ∑ i, C (L (Pi.single i 1))*X i

noncomputable def affinePoly {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : ZMod 2) : MvPolynomial (Fin n) (ZMod 2) := C c+linearPoly L

theorem evaluation {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : Fin n → ZMod 2) :
    eval x (linearPoly L)=L x := by
  have hx : (∑ i : Fin n, (x i) • (Pi.single i 1 : Fin n → ZMod 2))=x := by
    funext j
    simp [Pi.single_apply]
  calc
    _ = ∑ i, L (Pi.single i 1)*x i := by simp [linearPoly]
    _ = L (∑ i, (x i) • (Pi.single i 1 : Fin n → ZMod 2)) := by
      rw [map_sum]
      simp only [map_smul,smul_eq_mul]
      exact Finset.sum_congr rfl (fun i hi => mul_comm _ _)
    _ = _ := congrArg L hx

theorem affine_evaluation {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : ZMod 2) (x : Fin n → ZMod 2) : eval x (affinePoly L c)=c+L x := by
  simp only [affinePoly,map_add,eval_C,evaluation]

theorem degree_le_one {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (linearPoly L).totalDegree≤1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by simp)

theorem affine_degree_le_one {n : ℕ} (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : ZMod 2) :
    (affinePoly L c).totalDegree≤1 :=
  (totalDegree_add _ _).trans (max_le (by simp) (degree_le_one L))

end SemAC02.Supplement.P2MLinearFunctionalPolynomials
end

section
-- Inlined Solutions.P2MAffineCircuitForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffineCircuitForms

open MvPolynomial ACirc P2MArithmeticCircuitBasics

noncomputable def leafLinear {n : ℕ} : ACirc (ZMod 2) (Fin n) →
    ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  | .var i => LinearMap.proj i
  | _ => 0

def leafConstant {n : ℕ} : ACirc (ZMod 2) (Fin n) → ZMod 2
  | .const a => a
  | _ => 0

noncomputable def linearPart {n : ℕ} : ACirc (ZMod 2) (Fin n) →
    ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  | .sum ps => (ps.map (fun p => p.1 • leafLinear p.2)).sum
  | _ => 0

def constantPart {n : ℕ} : ACirc (ZMod 2) (Fin n) → ZMod 2
  | .sum ps => (ps.map (fun p => p.1*leafConstant p.2)).sum
  | _ => 0

lemma leaf_evaluation {n : ℕ} (c : ACirc (ZMod 2) (Fin n)) (hc : IsLeaf c) (x : Fin n → ZMod 2) :
    eval x c.toPoly=leafConstant c+leafLinear c x := by
  cases c with
  | var i => simp [toPoly,leafConstant,leafLinear]
  | const a => simp [toPoly,leafConstant,leafLinear]
  | sum ps => exact hc.elim
  | prod cs => exact hc.elim

lemma linearPart_apply {n : ℕ} (ps : List (ZMod 2×ACirc (ZMod 2) (Fin n))) (x : Fin n → ZMod 2) :
    linearPart (.sum ps) x=(ps.map (fun p => p.1*leafLinear p.2 x)).sum := by
  induction ps with
  | nil => simp [linearPart]
  | cons p ps ih => simpa only [linearPart,List.map_cons,List.sum_cons,LinearMap.add_apply,
      LinearMap.smul_apply,smul_eq_mul] using congrArg (fun z => p.1*leafLinear p.2 x+z) ih

theorem evaluation {n : ℕ} (c : ACirc (ZMod 2) (Fin n)) (hc : IsSumOf IsLeaf c)
    (x : Fin n → ZMod 2) : eval x c.toPoly=constantPart c+linearPart c x := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [linearPart_apply]
    change eval x (ACirc.sum ps).toPoly=(ps.map (fun p => p.1*leafConstant p.2)).sum+_
    rw [toPoly_sum,map_list_sum]
    simp only [List.map_map,Function.comp_def,map_mul,eval_C]
    calc
      _ = (ps.map (fun p => p.1*(leafConstant p.2+leafLinear p.2 x))).sum := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [leaf_evaluation p.2 (hc p hp) x]
      _ = _ := by simp only [mul_add,List.sum_map_add]

end SemAC02.Supplement.P2MAffineCircuitForms
end

section
-- Inlined Solutions.P2MBooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.P2MBooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.P2MBooleanAlgebra
end

section
-- Inlined Solutions.P2MMajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace AC02Frege.P2MMajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.P2MMajorityFoundation
end

section
-- Inlined Solutions.P2MBooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation

namespace AC02Frege.P2MBooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.P2MBooleanBasis
end

section
-- Inlined Solutions.P2MBooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation AC02Frege.P2MBooleanBasis

namespace AC02Frege.P2MBooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.P2MBooleanFlip
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.P2MSupport

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.P2MSupport
end

section
-- Inlined Solutions.P2MBooleanPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.P2MBooleanPC
end

section
-- Inlined Solutions.P2MRelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.P2MBooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.P2MBooleanLocality
end

section
-- Inlined Solutions.P2MBooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip

namespace AC02Frege.P2MBooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (P2MBooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := P2MBooleanFlip.flip
  map_add' p q := by simp only [P2MBooleanFlip.flip, map_add]
  map_smul' c p := by simp only [P2MBooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    P2MBooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.P2MBooleanRestrictions
end

section
-- Inlined Solutions.P2MCommonBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanRestrictions

namespace SemAC02.P2MCommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (P2MBooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : P2MBooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (P2MBooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (P2MBooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = P2MBooleanFlip.flip (P2MBooleanFlip.flip p) := (flip_involution p hml).symm
    _ = P2MBooleanFlip.flip 0 := congrArg (P2MBooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [P2MBooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.P2MCommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.P2MCommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace P2MProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end P2MProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MFibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.P2MFibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis

namespace SemAC02.P2MFibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.P2MFibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact P2MProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.P2MProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MCoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.P2MCoordinateSpaces
end

section
-- Inlined Solutions.P2MBooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.P2MMajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := P2MBooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.P2MCoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.P2MCoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.P2MBooleanFunctionPolynomials
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MProductCoordinates SemAC02.P2MCoordinateSpaces SemAC02.P2MBooleanLocality

namespace SemAC02.P2MMonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.P2MMonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MCoordinateSpaces SemAC02.P2MMonomialLocality

namespace SemAC02.P2MCoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.P2MCoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates SemAC02.P2MCoordinateSpaces
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MCoefficientControl

namespace SemAC02.P2MCoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.P2MCoefficientPolynomials
end

section
-- Inlined Solutions.P2MRelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MRelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : P2MRelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    P2MRelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply P2MRelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.P2MRelativeSpaceAlgebra
end

section
-- Inlined Solutions.P2MBooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.P2MBooleanDimension
end

section
-- Inlined Solutions.P2MMultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MMultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.P2MMultiplierSupportCount
end

section
-- Inlined Solutions.P2MBooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact P2MMultiplierSupportCount.low_support_card V K

end SemAC02.P2MBooleanDegreeBasis
end

section
-- Inlined Solutions.P2MBooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.P2MBooleanDegreeSpaces
end

section
-- Inlined Solutions.P2MAffinePolynomialPullback

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffinePolynomialPullback

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MLinearFunctionalPolynomials P2MBooleanDegreeSpaces

noncomputable def substitution {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (i : Fin n) :
    MvPolynomial (Fin m) (ZMod 2) := affinePoly ((LinearMap.proj i).comp A) (a i)

noncomputable def pullback {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin m) (ZMod 2) :=
  ML.comp (aeval (substitution a A)).toLinearMap

theorem degree_le {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : MvPolynomial (Fin n) (ZMod 2)) :
    (pullback a A p).totalDegree≤p.totalDegree := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  rw [aeval_eq_bind₁]
  exact P2MBooleanFlip.bind_linear_totalDegree_le (substitution a A)
    (fun i => affine_degree_le_one _ _) p

theorem evaluation {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : MvPolynomial (Fin n) (ZMod 2))
    (t : Fin m → ZMod 2) : eval t (pullback a A p)=eval (a+A t) p := by
  change eval t (ML (aeval (substitution a A) p))=_
  rw [eval_ml,map_aeval]
  have he : (eval t).comp (algebraMap (ZMod 2) (MvPolynomial (Fin m) (ZMod 2)))=RingHom.id (ZMod 2) := by
    ext c
    simp
  rw [he]
  change eval (fun i => eval t (substitution a A i)) p=eval (a+A t) p
  have hg : (fun i => eval t (substitution a A i))=a+A t := by
    funext i
    exact affine_evaluation _ _ _
  rw [hg]

noncomputable def bounded {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ℕ) :
    Ble (Fin n) k →ₗ[ZMod 2] Ble (Fin m) k :=
  LinearMap.codRestrict (Ble (Fin m) k) ((pullback a A).comp (Ble (Fin n) k).subtype) (by
    intro p
    exact (mem_Ble_iff k _).mpr ⟨ml_multilinear _,(degree_le a A (p : MvPolynomial (Fin n) (ZMod 2))).trans
      ((mem_Ble_iff k (p : MvPolynomial (Fin n) (ZMod 2))).mp p.2).2⟩)

theorem rank_le {n m : ℕ} (a : Fin n → ZMod 2)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range (bounded a A k))≤Hn m k := by
  have hh := (LinearMap.range (bounded a A k)).finrank_le
  simpa only [P2MBooleanDegreeBasis.finrank_Ble,Fintype.card_fin] using hh

end SemAC02.Supplement.P2MAffinePolynomialPullback
end

section
-- Inlined Solutions.P2MAffineFiberIndicator

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffineFiberIndicator

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MLinearFunctionalPolynomials Classical

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma product_test {I : Type} [Fintype I] (f g : I → ZMod 2) :
    (∏ i, (1+f i+g i))=if f=g then 1 else 0 := by
  classical
  by_cases he : f=g
  · subst g
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i hi
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
  · rw [if_neg he]
    have hex : ∃ i, f i≠g i := by
      by_contra hn
      push_neg at hn
      exact he (funext hn)
    obtain ⟨i,hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases zero_or_one (f i) with hf | hf <;> rcases zero_or_one (g i) with hg | hg
    all_goals simp_all [CharTwo.add_self_eq_zero]

noncomputable def coordinates {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) (LinearMap.range L)) → ZMod 2) :=
  (Module.finBasis (ZMod 2) (LinearMap.range L)).equivFun.toLinearMap.comp L.rangeRestrict

noncomputable def coordinate {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (i : Fin (Module.finrank (ZMod 2) (LinearMap.range L))) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i).comp (coordinates L)

lemma coordinates_eq_iff {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (x y : Fin n → ZMod 2) :
    coordinates L x=coordinates L y ↔ L x=L y := by
  change (Module.finBasis (ZMod 2) (LinearMap.range L)).equivFun (L.rangeRestrict x)=
    (Module.finBasis (ZMod 2) (LinearMap.range L)).equivFun (L.rangeRestrict y) ↔ _
  constructor
  · intro h
    exact congrArg Subtype.val ((Module.finBasis (ZMod 2) (LinearMap.range L)).equivFun.injective h)
  · intro h
    exact congrArg (Module.finBasis (ZMod 2) (LinearMap.range L)).equivFun (Subtype.ext h)

noncomputable def indicator {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (a : Fin n → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) :=
  ML (∏ i : Fin (Module.finrank (ZMod 2) (LinearMap.range L)), affinePoly (coordinate L i) (1+coordinate L i a))

theorem degree_bound {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (a : Fin n → ZMod 2) :
    (indicator L a).totalDegree≤Module.finrank (ZMod 2) (LinearMap.range L) := by
  apply (P2MBooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin (Module.finrank (ZMod 2) (LinearMap.range L)), 1 :=
      Finset.sum_le_sum (fun i hi => affine_degree_le_one _ _)
    _ = _ := by simp

theorem evaluation {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (a x : Fin n → ZMod 2) :
    eval x (indicator L a)=if L x=L a then 1 else 0 := by
  classical
  rw [indicator,eval_ml,map_prod]
  simp only [affine_evaluation]
  have hp := product_test (coordinates L x) (coordinates L a)
  simp only [coordinates_eq_iff] at hp
  convert hp using 1
  apply Finset.prod_congr rfl
  intro i hi
  change (1+coordinate L i a)+coordinate L i x=1+coordinate L i x+coordinate L i a
  ring

end SemAC02.Supplement.P2MAffineFiberIndicator
end

section
-- Inlined Solutions.P2MAffineFiberRestriction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MAffineFiberRestriction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

noncomputable def parameter {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) :
    (Fin (Module.finrank (ZMod 2) (LinearMap.ker L)) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (LinearMap.ker L).subtype.comp
    (Module.finBasis (ZMod 2) (LinearMap.ker L)).equivFun.symm.toLinearMap

theorem parameter_zero {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W)
    (t : Fin (Module.finrank (ZMod 2) (LinearMap.ker L)) → ZMod 2) : L (parameter L t)=0 :=
  ((Module.finBasis (ZMod 2) (LinearMap.ker L)).equivFun.symm t).2

theorem exists_parameter {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (a x : Fin n → ZMod 2) (h : L x=L a) :
    ∃ t, a+parameter L t=x := by
  have hz : x-a∈LinearMap.ker L := by simp only [LinearMap.mem_ker,map_sub,h,sub_self]
  let z : LinearMap.ker L := ⟨x-a,hz⟩
  let t := (Module.finBasis (ZMod 2) (LinearMap.ker L)).equivFun z
  have he : parameter L t=x-a := by
    change (((Module.finBasis (ZMod 2) (LinearMap.ker L)).equivFun.symm
      ((Module.finBasis (ZMod 2) (LinearMap.ker L)).equivFun z) : LinearMap.ker L) : Fin n → ZMod 2)=_
    rw [LinearEquiv.symm_apply_apply]
  exact ⟨t,by rw [he]; abel⟩

theorem rank_nullity {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) :
    Module.finrank (ZMod 2) (LinearMap.range L)+Module.finrank (ZMod 2) (LinearMap.ker L)=n := by
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using LinearMap.finrank_range_add_finrank_ker L

theorem kernel_annihilates {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] W) (a : Fin n → ZMod 2)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : P2MAffinePolynomialPullback.pullback a (parameter L) p=0) :
    ML (p*P2MAffineFiberIndicator.indicator L a)=0 := by
  apply multilinear_ext (ml_multilinear _) (by simpa using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)))
  intro x
  rw [eval_ml,map_mul,P2MAffineFiberIndicator.evaluation,map_zero]
  by_cases he : L x=L a
  · rw [if_pos he,mul_one]
    obtain ⟨t,ht⟩ := exists_parameter L a x he
    have hh := congrArg (eval t) hp
    simpa only [P2MAffinePolynomialPullback.evaluation,ht,map_zero] using hh
  · simp only [if_neg he,mul_zero]

end SemAC02.Supplement.P2MAffineFiberRestriction
end

section
-- Inlined Solutions.P2MProductAffineFiber

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MProductAffineFiber

open MvPolynomial ACirc P2MArithmeticCircuitBasics AC02Frege AC02Frege.P2MBooleanAlgebra

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma list_prod_one_iff (xs : List (ZMod 2)) : xs.prod=1 ↔ ∀ x∈xs, x=1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases zero_or_one x with hx | hx
    · simp [hx]
    · simp [hx,ih]

noncomputable def termPoly {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n))) :
    MvPolynomial (Fin n) (ZMod 2) := ML (ACirc.prod cs).toPoly

noncomputable def formsMap {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n))) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin cs.length → ZMod 2) :=
  LinearMap.pi (fun i => P2MAffineCircuitForms.linearPart cs[i])

lemma forms_eq_iff {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n))) (x a : Fin n → ZMod 2) :
    formsMap cs x=formsMap cs a ↔
      ∀ c∈cs, P2MAffineCircuitForms.linearPart c x=P2MAffineCircuitForms.linearPart c a := by
  constructor
  · intro h c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
    exact congrFun h (⟨i,hi⟩ : Fin cs.length)
  · intro h
    funext i
    exact h cs[i] (List.getElem_mem i.isLt)

lemma value_one_iff {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n))) (x : Fin n → ZMod 2) :
    eval x (termPoly cs)=1 ↔ ∀ c∈cs, eval x c.toPoly=1 := by
  rw [termPoly,eval_ml,toPoly_prod,map_list_prod,list_prod_one_iff]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]

theorem exists_fiber {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n)))
    (hcs : ∀ c∈cs, IsSumOf IsLeaf c) (hT : termPoly cs≠0) :
    ∃ a : Fin n → ZMod 2, termPoly cs=P2MAffineFiberIndicator.indicator (formsMap cs) a := by
  classical
  have hex : ∃ a : Fin n → ZMod 2, eval a (termPoly cs)≠0 := by
    by_contra hn
    push_neg at hn
    apply hT
    apply multilinear_ext (ml_multilinear _) (by simpa using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)))
    intro a
    simpa only [termPoly,map_zero] using hn a
  obtain ⟨a,ha⟩ := hex
  have ha1 : eval a (termPoly cs)=1 := (zero_or_one _).resolve_left ha
  have hforms := (value_one_iff cs a).mp ha1
  have hiff (x : Fin n → ZMod 2) : eval x (termPoly cs)=1 ↔ formsMap cs x=formsMap cs a := by
    rw [value_one_iff,forms_eq_iff]
    constructor
    · intro hx c hc
      apply add_left_cancel (a := P2MAffineCircuitForms.constantPart c)
      rw [←P2MAffineCircuitForms.evaluation c (hcs c hc) x,←P2MAffineCircuitForms.evaluation c (hcs c hc) a,
        hx c hc,hforms c hc]
    · intro hx c hc
      rw [P2MAffineCircuitForms.evaluation c (hcs c hc) x,hx c hc,
        ←P2MAffineCircuitForms.evaluation c (hcs c hc) a]
      exact hforms c hc
  refine ⟨a,?_⟩
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  change eval x (termPoly cs)=eval x (P2MAffineFiberIndicator.indicator (formsMap cs) a)
  rw [P2MAffineFiberIndicator.evaluation]
  by_cases he : formsMap cs x=formsMap cs a
  · rw [if_pos he]
    exact (hiff x).mpr he
  · rw [if_neg he]
    rcases zero_or_one (eval x (termPoly cs)) with hz | ho
    · exact hz
    · exact False.elim (he ((hiff x).mp ho))

theorem degree_bound {n : ℕ} (cs : List (ACirc (ZMod 2) (Fin n)))
    (hcs : ∀ c∈cs, IsSumOf IsLeaf c) (hT : termPoly cs≠0) :
    (termPoly cs).totalDegree≤Module.finrank (ZMod 2) (LinearMap.range (formsMap cs)) := by
  obtain ⟨a,ha⟩ := exists_fiber cs hcs hT
  rw [ha]
  exact P2MAffineFiberIndicator.degree_bound _ _

end SemAC02.Supplement.P2MProductAffineFiber
end

section
-- Inlined Solutions.P2MSPSTermData

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSTermData

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra

structure Model (n k : ℕ) (T : MvPolynomial (Fin n) (ZMod 2)) where
  freeVariables : ℕ
  freeVariables_le : freeVariables≤n
  multilinear : IsMultilinear T
  degree : T.totalDegree≤n-freeVariables
  restriction : Ble (Fin n) k →ₗ[ZMod 2] Ble (Fin freeVariables) k
  annihilates : ∀ f : Ble (Fin n) k, restriction f=0 → ML ((f : MvPolynomial (Fin n) (ZMod 2))*T)=0

theorem product {n : ℕ} (k : ℕ) (cs : List (ACirc (ZMod 2) (Fin n)))
    (hcs : ∀ c∈cs, IsSumOf IsLeaf c) (hT : P2MProductAffineFiber.termPoly cs≠0) :
    Nonempty (Model n k (P2MProductAffineFiber.termPoly cs)) := by
  obtain ⟨a,ha⟩ := P2MProductAffineFiber.exists_fiber cs hcs hT
  let L := P2MProductAffineFiber.formsMap cs
  let m := Module.finrank (ZMod 2) (LinearMap.ker L)
  have hrank := P2MAffineFiberRestriction.rank_nullity L
  have hm : m≤n := by dsimp [m]; omega
  have hdegree : (P2MProductAffineFiber.termPoly cs).totalDegree≤n-m := by
    have hh : (P2MProductAffineFiber.termPoly cs).totalDegree≤Module.finrank (ZMod 2) (LinearMap.range L) :=
      P2MProductAffineFiber.degree_bound cs hcs hT
    change Module.finrank (ZMod 2) (LinearMap.range L)+m=n at hrank
    omega
  refine ⟨⟨m,hm,ml_multilinear _,hdegree,
    P2MAffinePolynomialPullback.bounded a (P2MAffineFiberRestriction.parameter L) k,?_⟩⟩
  intro f hf
  have hz : P2MAffinePolynomialPullback.pullback a (P2MAffineFiberRestriction.parameter L)
      (f : MvPolynomial (Fin n) (ZMod 2))=0 := congrArg Subtype.val hf
  rw [ha]
  exact P2MAffineFiberRestriction.kernel_annihilates L a f hz

theorem term {n : ℕ} (k : ℕ) (t : ACirc (ZMod 2) (Fin n))
    (ht : IsProdOf (IsSumOf IsLeaf) t) (hT : ML t.toPoly≠0) :
    Nonempty (Model n k (ML t.toPoly)) := by
  cases t with
  | var i => exact ht.elim
  | const a => exact ht.elim
  | sum ps => exact ht.elim
  | prod cs => exact product k cs ht hT

end SemAC02.Supplement.P2MSPSTermData
end

section
-- Inlined Solutions.P2MSmallCumulativeBinomial

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSmallCumulativeBinomial

open Finset

theorem mono_variables {m N : ℕ} (hm : m ≤ N) (k : ℕ) : Hn m k ≤ Hn N k := by
  unfold Hn
  calc
    _  ≤  ∑ j∈range (min k m+1), N.choose j := sum_le_sum (fun j hj => Nat.choose_le_choose j hm)
    _  ≤  _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; omega)

theorem twice_choose (m k : ℕ) (hkm : 3*k ≤ m) : Hn m k ≤ 2*m.choose k := by
  induction k with
  | zero => simp [Hn]
  | succ k ih =>
    have hik : 3*k ≤ m := by omega
    have ih' := ih hik
    have hk : k ≤ m := by omega
    have hks : k+1 ≤ m := by omega
    have hsum : Hn m (k+1)=Hn m k+m.choose (k+1) := by
      simp only [Hn,min_eq_left hk,min_eq_left hks]
      exact sum_range_succ _ _
    have hr := Nat.choose_succ_right_eq m k
    have hgap : 2*(k+1) ≤ m-k := by omega
    have hmul := Nat.mul_le_mul_right (m.choose k) hgap
    have hchoose : 2*m.choose k ≤ m.choose (k+1) := by nlinarith
    rw [hsum]
    omega

theorem uniform_bound {m N k : ℕ} (hm : m ≤ N) (hk : 3*k ≤ N) : Hn m k ≤ 2*N.choose k :=
  (mono_variables hm k).trans (twice_choose N k hk)

end SemAC02.Supplement.P2MSmallCumulativeBinomial
end

section
-- Inlined Solutions.P2MLinearMapFactorThrough

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace P2MProofComplexity.P2MLinearMapFactorThrough

/-- A map that kills every relation killed by f extends to a linear map on f's codomain. -/
theorem exists_factor {K A W Z : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (f : A →ₗ[K] W) (g : A →ₗ[K] Z) (h : f.ker ≤ g.ker) :
    ∃ H : W →ₗ[K] Z, H.comp f = g := by
  let L := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨H,hH⟩ := LinearMap.exists_extend L
  refine ⟨H,?_⟩
  ext x
  calc
    H (f x) = L (f.rangeRestrict x) := by
      have he : f.range.subtype (f.rangeRestrict x) = f x := rfl
      have hh := LinearMap.congr_fun hH (f.rangeRestrict x)
      rw [LinearMap.comp_apply,he] at hh
      exact hh
    _ = g x := by
      change (f.ker.liftQ g h) (f.quotKerEquivRange.symm ⟨f x,?_⟩) = g x
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl

end P2MProofComplexity.P2MLinearMapFactorThrough
end

section
-- Inlined Solutions.P2MLinearMapCommonKernelWitness

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MLinearMapCommonKernelWitness

open Module

theorem exists_nonzero_image {K X W I : Type} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module.Finite K X] [Fintype I]
    (Y : I → Type) [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)] [∀ i, Module.Finite K (Y i)]
    (R : X →ₗ[K] W) (f : ∀ i, X →ₗ[K] Y i)
    (hrank : (∑ i, finrank K (Y i))<finrank K (LinearMap.range R)) :
    ∃ x : X, R x≠0 ∧ ∀ i, f i x=0 := by
  classical
  by_contra hn
  let C := LinearMap.pi f
  have hker : LinearMap.ker C≤LinearMap.ker R := by
    intro x hx
    change R x=0
    by_contra hR
    apply hn
    refine ⟨x,hR,?_⟩
    intro i
    exact congrFun (show C x=0 from hx) i
  obtain ⟨H,hH⟩ := P2MLinearMapFactorThrough.exists_factor C R hker
  have hrange : R.range≤H.range := by
    rw [←hH]
    exact LinearMap.range_comp_le_range _ _
  have hdim : finrank K R.range≤finrank K ((i : I) → Y i) :=
    (Submodule.finrank_mono hrange).trans H.finrank_range_le
  rw [Module.finrank_pi_fintype] at hdim
  omega

end P2MProofComplexity.P2MLinearMapCommonKernelWitness
end

section
-- Inlined Solutions.P2MSPSCommonMultiplierExistence

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSCommonMultiplierExistence

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra Module Classical

theorem exists_multiplier {n k r : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (E : Finset (MvPolynomial (Fin n) (ZMod 2))) (models : ∀ T : E, P2MSPSTermData.Model n k T.1)
    (R : Ble (Fin n) k →ₗ[ZMod 2] W) (hkr : 3*k≤n-r)
    (hrank : 2*(n-r).choose k*E.card<finrank (ZMod 2) R.range) :
    ∃ f : Ble (Fin n) k, R f≠0 ∧ ∀ T : E,
      T.1.totalDegree<r ∨ ML ((f : MvPolynomial (Fin n) (ZMod 2))*T.1)=0 := by
  let I := {T : E // r≤n-(models T).freeVariables}
  let Y (i : I) : Type := ↥(Ble (Fin (models i.1).freeVariables) k)
  let maps (i : I) : Ble (Fin n) k →ₗ[ZMod 2] Y i := (models i.1).restriction
  have hm (i : I) : (models i.1).freeVariables≤n-r := by
    have h₁ := (models i.1).freeVariables_le
    have h₂ := i.2
    omega
  have hdim : (∑ i : I, finrank (ZMod 2) (Y i))≤2*(n-r).choose k*E.card := by
    have hic : Fintype.card I≤E.card := by
      exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_coe _)
    calc
      _ = ∑ i : I, Hn (models i.1).freeVariables k := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [Y,Fintype.card_fin] using P2MBooleanDegreeBasis.finrank_Ble (Fin (models i.1).freeVariables) k
      _ ≤ ∑ _i : I, 2*(n-r).choose k := Finset.sum_le_sum (fun i hi =>
        P2MSmallCumulativeBinomial.uniform_bound (hm i) hkr)
      _ = 2*(n-r).choose k*Fintype.card I := by simp [Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hic
  obtain ⟨f,hR,hkill⟩ := P2MProofComplexity.P2MLinearMapCommonKernelWitness.exists_nonzero_image Y R maps
    (hdim.trans_lt hrank)
  refine ⟨f,hR,?_⟩
  intro T
  by_cases hhigh : r≤n-(models T).freeVariables
  · exact Or.inr ((models T).annihilates f (hkill (⟨T,hhigh⟩ : I)))
  · exact Or.inl ((models T).degree.trans_lt (lt_of_not_ge hhigh))

end SemAC02.Supplement.P2MSPSCommonMultiplierExistence
end

section
-- Inlined Solutions.P2MPseudoReductionSoundness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionSoundness

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces

theorem multilinear_lines {V : Type} (F : Set (MvPolynomial V (ZMod 2)))
    (π : List (MvPolynomial V (ZMod 2))) (hπ : PCNonBool.IsDerivation ML F π) :
    ∀ p∈π, IsMultilinear p := by
  have hz : ∀ k (hk : k<π.length), ML π[k]=π[k] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨f,hf,a,he⟩ | ⟨i,j,hi,hj,a,b,he⟩ | ⟨i,hi,v,he⟩
      · rw [he,map_smul,ml_of_multilinear _ (ml_multilinear _)]
      · rw [he,map_add,map_smul,map_smul,ih i hi (hi.trans hk),ih j hj (hj.trans hk)]
      · rw [he,ml_of_multilinear _ (ml_multilinear _)]
  intro p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hp
  rw [←hz k hk]
  exact ml_multilinear _

theorem derivation {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial V (ZMod 2))) (R : Ble V B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (hF : ∀ f∈F, f∈Ble V B) (π : List (MvPolynomial V (ZMod 2)))
    (hπ : PCNonBool.IsDerivation ML F π) (hBle : ∀ p∈π, p∈Ble V B) :
    ∀ p (hp : p∈π), R ⟨p,hBle p hp⟩=0 := by
  have hz : ∀ k (hk : k<π.length), R ⟨π[k],hBle _ (List.getElem_mem hk)⟩=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ k hk with ⟨f,hf,a,he⟩ | ⟨i,j,hi,hj,a,b,he⟩ | ⟨i,hi,v,he⟩
      · have hml := ((mem_Ble_iff B f).mp (hF f hf)).1
        have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=a • ⟨f,hF f hf⟩ := by
          apply Subtype.ext
          simpa only [Submodule.coe_smul,ml_of_multilinear f hml] using he
        rw [he',map_smul,hR.1 f hf (hF f hf),smul_zero]
      · have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=
            a • ⟨π[i],hBle _ (List.getElem_mem (hi.trans hk))⟩+
            b • ⟨π[j],hBle _ (List.getElem_mem (hj.trans hk))⟩ := Subtype.ext he
        rw [he',map_add,map_smul,map_smul,ih i hi (hi.trans hk),ih j hj (hj.trans hk)]
        simp
      · have hb : ML (X v*π[i])∈Ble V B := by rw [←he]; exact hBle _ (List.getElem_mem hk)
        have hh := hR.2 ⟨π[i],hBle _ (List.getElem_mem (hi.trans hk))⟩ v hb (ih i hi (hi.trans hk))
        have he' : (⟨π[k],hBle _ (List.getElem_mem hk)⟩ : Ble V B)=⟨ML (X v*π[i]),hb⟩ := Subtype.ext he
        rwa [he']
  intro p hp
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact hz k hk

end SemAC02.Supplement.P2MPseudoReductionSoundness
end

section
-- Inlined Solutions.P2MGenericPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MGenericPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation LinearMap.id P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : p.totalDegree ≤ D) : Derivable P D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P D u)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) : Derivable P D (u * v) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    simpa only [mul_comm u (C c), ← smul_eq_C_mul] using pc_smul P D hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add]
    exact pc_add P D (ihm (by omega)) (ihp (by omega))
  | mul_X p i ih =>
    by_cases hp : p = 0
    · simp only [hp, zero_mul, mul_zero]; exact pc_zero P D
    have hdp : (p * X i).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
    have hbound : u.totalDegree + p.totalDegree + 1 ≤ D := by omega
    have hmul : (u * p).totalDegree + 1 ≤ D := by
      have := totalDegree_mul u p
      omega
    simpa only [mul_assoc] using pc_mul_X P D (ih (by omega)) i hmul

end SemAC02.P2MGenericPC
end

section
-- Inlined Solutions.PCBooleanReduction

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MGenericPC

theorem map_multilinear_derivation {n : ℕ}
    (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (π : List (MvPolynomial (Fin n) (ZMod 2)))
    (hπ : PCNonBool.IsDerivation LinearMap.id P π) :
    PCNonBool.IsDerivation ML P (π.map ML) := by
  intro k hk
  have hk' : k < π.length := by simpa only [List.length_map] using hk
  rcases hπ k hk' with ha | hc | hm
  · obtain ⟨a, ha, c, hac⟩ := ha
    left
    refine ⟨a, ha, c, ?_⟩
    simp only [List.getElem_map, hac, LinearMap.id_apply, map_smul]
  · obtain ⟨i, j, hi, hj, c, d, hij⟩ := hc
    right; left
    refine ⟨i, j, hi, hj, c, d, ?_⟩
    simp only [List.getElem_map, hij, map_add, map_smul]
  · obtain ⟨i, hi, v, hiv⟩ := hm
    right; right
    refine ⟨i, hi, v, ?_⟩
    simp only [List.getElem_map, hiv, LinearMap.id_apply]
    rw [ml_mul_right]

theorem derivable_multilinearized {n : ℕ}
    (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (a : MvPolynomial (Fin n) (ZMod 2)) (ha : a ∈ P)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : Derivable P D p) :
    ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
      PCNonBool.IsDerivation ML P π ∧ ML p ∈ π ∧ ∀ q ∈ π, q.totalDegree ≤ D := by
  classical
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · refine ⟨[0], ?_, by simp, ?_⟩
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      left
      exact ⟨a, ha, 0, by simp⟩
    · intro q hq
      have hq0 : q = 0 := by simpa using hq
      subst q
      simp
  · refine ⟨π.map ML, map_multilinear_derivation P π hπ, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact (ml_totalDegree_le r).trans (hdeg r hr)

end SemAC02.P2MGenericPC
end

section
-- Inlined Solutions.P2MPseudoReductionMultipliers

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionMultipliers

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces P2MPseudoReductionSoundness P2MGenericPC

theorem axiom_product {n B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n) (ZMod 2))) (R : Ble (Fin n) B →ₗ[ZMod 2] W)
    (hR : IsPseudoRed F R) (hF : ∀ f∈F, f∈Ble (Fin n) B)
    (f u : MvPolynomial (Fin n) (ZMod 2)) (hf : f∈F)
    (hdeg : f.totalDegree+u.totalDegree≤B) (hprod : ML (f*u)∈Ble (Fin n) B) :
    R ⟨ML (f*u),hprod⟩=0 := by
  have ha := pc_axiom F B f hf (by omega)
  have hm := pc_polynomial_mul F B f u ha hdeg
  obtain ⟨τ,hτ,hmem,hdegree⟩ := derivable_multilinearized F B f hf (f*u) hm
  have hBle : ∀ p∈τ, p∈Ble (Fin n) B := by
    intro p hp
    exact (mem_Ble_iff B p).mpr ⟨multilinear_lines F τ hτ p hp,hdegree p hp⟩
  exact derivation F R hR hF τ hτ hBle _ hmem

theorem polyFn_ext {n : ℕ} {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q) (he : ∀ x, polyFn p x=polyFn q x) : p=q := by
  apply multilinear_ext hp hq
  intro x
  let y : Fin n → Bool := fun i => decide (x i=1)
  have hy : (boolPt y : Fin n → ZMod 2)=x := by
    funext i
    rcases P2MMajorityFoundation.eq_zero_or_one (x i) with hi | hi <;> simp [boolPt,y,hi]
  have hh := he y
  simpa only [polyFn,hy] using hh

noncomputable def multiplied {n : ℕ} (f : MvPolynomial (Fin n) (ZMod 2))
    (c : ACirc (ZMod 2) (Fin n)) : MvPolynomial (Fin n) (ZMod 2) := ML (f*c.toPoly)

lemma multiplied_value {n : ℕ} (f : MvPolynomial (Fin n) (ZMod 2))
    (c : ACirc (ZMod 2) (Fin n)) (x : Fin n → Bool) :
    polyFn (multiplied f c) x=polyFn f x*cval c x := by
  simp only [multiplied,polyFn,eval_ml,map_mul,cval]

end SemAC02.Supplement.P2MPseudoReductionMultipliers
end

section
-- Inlined Solutions.P2MSPSTopPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSTopPolynomials

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra Classical

noncomputable def pool {n : ℕ} (π : List (ACirc (ZMod 2) (Fin n))) :
    Finset (MvPolynomial (Fin n) (ZMod 2)) :=
  ((π.flatMap topTerms).map (fun t => ML t.toPoly)).toFinset.filter (fun p => p≠0)

theorem mem_pool {n : ℕ} (π : List (ACirc (ZMod 2) (Fin n))) (p : MvPolynomial (Fin n) (ZMod 2)) :
    p∈pool π ↔ p≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, ML t.toPoly=p := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem multilinear {n : ℕ} (π : List (ACirc (ZMod 2) (Fin n)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p∈pool π) : IsMultilinear p := by
  obtain ⟨_,c,hc,t,ht,rfl⟩ := (mem_pool π p).mp hp
  exact ml_multilinear _

lemma top_term_layer {n : ℕ} (c t : ACirc (ZMod 2) (Fin n)) (hc : IsSPS c) (ht : t∈topTerms c) :
    IsProdOf (IsSumOf IsLeaf) t := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    exact hc p hp

theorem model_exists {n : ℕ} (π : List (ACirc (ZMod 2) (Fin n))) (hπ : ∀ c∈π, IsSPS c)
    (k : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p∈pool π) : Nonempty (P2MSPSTermData.Model n k p) := by
  obtain ⟨hn,c,hc,t,ht,rfl⟩ := (mem_pool π p).mp hp
  exact P2MSPSTermData.term k t (top_term_layer c t (hπ c hc) ht) hn

theorem card_le_topS {n : ℕ} (π : List (ACirc (ZMod 2) (Fin n))) : (pool π).card≤topS Set.univ π := by
  let Ω : Set (Fin n → Bool) := Set.univ
  let emb (p : MvPolynomial (Fin n) (ZMod 2)) : Ω → ZMod 2 := fun x => polyFn p x.1
  let S : Set (Ω → ZMod 2) := {g | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}
  have hinj : Set.InjOn emb (pool π : Set (MvPolynomial (Fin n) (ZMod 2))) := by
    intro p hp q hq he
    apply P2MPseudoReductionMultipliers.polyFn_ext (multilinear π p hp) (multilinear π q hq)
    intro x
    exact congrFun he (⟨x,Set.mem_univ x⟩ : Ω)
  have hcard := Finset.card_image_of_injOn hinj
  have hsub : (↑((pool π).image emb) : Set (Ω → ZMod 2))⊆S := by
    intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hn,c,hc,t,ht,he⟩ := (mem_pool π p).mp hp
    constructor
    · intro hz
      apply hn
      apply P2MPseudoReductionMultipliers.polyFn_ext (multilinear π p hp)
        (by simpa using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)))
      intro x
      have hh := congrFun hz (⟨x,Set.mem_univ x⟩ : Ω)
      simpa only [emb,Pi.zero_apply,polyFn,map_zero] using hh
    · refine ⟨c,hc,t,ht,?_⟩
      funext x
      rw [←he]
      simp only [emb,polyFn,eval_ml,cval]
  let U : Finset (Ω → ZMod 2) := (π.flatMap topTerms).toFinset.image (fun t => fun x => cval t x.1)
  have hS : S⊆(↑U : Set (Ω → ZMod 2)) := by
    rintro g ⟨hg,c,hc,t,ht,rfl⟩
    exact Finset.mem_image.mpr ⟨t,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,ht⟩),rfl⟩
  have hfin : S.Finite := (Finset.finite_toSet U).subset hS
  have hh := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset,hcard] at hh
  exact hh

end SemAC02.Supplement.P2MSPSTopPolynomials
end

section
-- Inlined Solutions.P2MSPSLineMultiplierDegree

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSLineMultiplierDegree

open MvPolynomial ACirc P2MArithmeticCircuitBasics AC02Frege AC02Frege.P2MBooleanAlgebra P2MPseudoReductionMultipliers

lemma expansion {n : ℕ} (f : MvPolynomial (Fin n) (ZMod 2))
    (ps : List (ZMod 2×ACirc (ZMod 2) (Fin n))) :
    multiplied f (.sum ps)=(ps.map (fun p => p.1 • ML (f*ML p.2.toPoly))).sum := by
  induction ps with
  | nil => simp [multiplied,toPoly_sum]
  | cons p ps ih =>
    have he : (ACirc.sum (p::ps)).toPoly=C p.1*p.2.toPoly+(ACirc.sum ps).toPoly := by
      simp only [toPoly_sum,List.map_cons,List.sum_cons]
    simp only [List.map_cons,List.sum_cons]
    change ML (f*(ACirc.sum (p::ps)).toPoly)=_
    rw [he,mul_add,map_add]
    have hp : f*(C p.1*p.2.toPoly)=p.1 • (f*p.2.toPoly) := by rw [smul_eq_C_mul]; ring
    rw [hp,map_smul,←ml_mul_right]
    exact congrArg (fun z => p.1 • ML (f*ML p.2.toPoly)+z) ih

lemma degree_sum {n : ℕ} (D : ℕ) (ps : List (MvPolynomial (Fin n) (ZMod 2)))
    (h : ∀ p∈ps, p.totalDegree≤D) : ps.sum.totalDegree≤D := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    exact (totalDegree_add _ _).trans (max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq]))))

lemma line_degree {n : ℕ} (f : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (c : ACirc (ZMod 2) (Fin n)) (hc : IsSPS c)
    (ht : ∀ t∈topTerms c, (ML (f*ML t.toPoly)).totalDegree≤D) :
    (multiplied f c).totalDegree≤D := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [expansion]
    apply degree_sum
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (totalDegree_smul_le _ _).trans (ht p.2 (List.mem_map.mpr ⟨p,hp,rfl⟩))

theorem proof_degree {n k r : ℕ} (π : List (ACirc (ZMod 2) (Fin n))) (hπ : ∀ c∈π, IsSPS c)
    (f : Ble (Fin n) k)
    (hkill : ∀ T : P2MSPSTopPolynomials.pool π,
      T.1.totalDegree<r ∨ ML ((f : MvPolynomial (Fin n) (ZMod 2))*T.1)=0) :
    ∀ c∈π, (multiplied f c).totalDegree≤k+r := by
  intro c hc
  apply line_degree f (k+r) c (hπ c hc)
  intro t ht
  by_cases hz : ML t.toPoly=0
  · simp only [hz,mul_zero,map_zero,totalDegree_zero,Nat.zero_le]
  · have hp : ML t.toPoly∈P2MSPSTopPolynomials.pool π :=
      (P2MSPSTopPolynomials.mem_pool π _).mpr ⟨hz,c,hc,t,ht,rfl⟩
    rcases hkill ⟨ML t.toPoly,hp⟩ with hlow | hzero
    · change (ML t.toPoly).totalDegree<r at hlow
      apply (P2MBooleanFlip.ml_totalDegree_le _).trans
      apply (totalDegree_mul _ _).trans
      have hf := ((P2MBooleanDegreeSpaces.mem_Ble_iff k (f : MvPolynomial (Fin n) (ZMod 2))).mp f.2).2
      omega
    · rw [hzero]
      simp

end SemAC02.Supplement.P2MSPSLineMultiplierDegree
end

section
-- Inlined Solutions.P2MPseudoReductionSemanticClosure

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionSemanticClosure

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces P2MPseudoReductionSoundness

theorem binary {n B d : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n) (ZMod 2))) (R : Ble (Fin n) B →ₗ[ZMod 2] W)
    (hR : IsPseudoRed F R) (hB : 3*d≤B)
    (p q g : MvPolynomial (Fin n) (ZMod 2))
    (hp : p∈Ble (Fin n) B) (hq : q∈Ble (Fin n) B) (hg : g∈Ble (Fin n) B)
    (hdp : p.totalDegree≤d) (hdq : q.totalDegree≤d) (hdg : g.totalDegree≤d)
    (hRp : R ⟨p,hp⟩=0) (hRq : R ⟨q,hq⟩=0)
    (hsem : ∀ x : Fin n → Bool, polyFn p x=0 → polyFn q x=0 → polyFn g x=0) :
    R ⟨g,hg⟩=0 := by
  classical
  have hmlp := ((mem_Ble_iff B p).mp hp).1
  have hmlq := ((mem_Ble_iff B q).mp hq).1
  have hmlg := ((mem_Ble_iff B g).mp hg).1
  have heval : ∀ x : Fin n → ZMod 2, eval x p=0 → eval x q=0 → eval x g=0 := by
    intro x hx₁ hx₂
    let y : Fin n → Bool := fun i => decide (x i=1)
    have he : (boolPt y : Fin n → ZMod 2)=x := by
      funext i
      rcases P2MMajorityFoundation.eq_zero_or_one (x i) with hi | hi <;> simp [boolPt,y,hi]
    have hh := hsem y
    change eval (boolPt y) p=0 → eval (boolPt y) q=0 → eval (boolPt y) g=0 at hh
    rw [he] at hh
    exact hh hx₁ hx₂
  obtain ⟨τ,hτ,hgτ,hdeg⟩ := (lemma_2_1_semantic_simulation d p q g hmlp hmlq hmlg hdp hdq hdg heval).2
  have hF' : ∀ f∈({p,q} : Set (MvPolynomial (Fin n) (ZMod 2))), f∈Ble (Fin n) B := by
    intro f hf
    rcases hf with rfl | hf
    · exact hp
    · have he : f=q := hf
      exact he ▸ hq
  have hR' : IsPseudoRed ({p,q} : Set (MvPolynomial (Fin n) (ZMod 2))) R := by
    refine ⟨?_,hR.2⟩
    intro f hf hfb
    rcases hf with rfl | hf
    · exact hRp
    · have he : f=q := hf
      subst f
      exact hRq
  have hBle : ∀ f∈τ, f∈Ble (Fin n) B := by
    intro f hf
    exact (mem_Ble_iff B f).mpr ⟨multilinear_lines _ τ hτ f hf,(hdeg f hf).trans hB⟩
  exact derivation {p,q} R hR' hF' τ hτ hBle g hgτ

end SemAC02.Supplement.P2MPseudoReductionSemanticClosure
end

section
-- Inlined Solutions.P2MSPSCommonMultiplierSoundness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSCommonMultiplierSoundness

open MvPolynomial ACirc AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces P2MPseudoReductionMultipliers

theorem no_annihilator {n B D k d₀ : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n) (ZMod 2))) (hF : ∀ f∈F, IsMultilinear f ∧ f.totalDegree≤d₀)
    (R : Ble (Fin n) B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R) (hB : 3*D≤B) (hbudget : k+d₀≤D)
    (f : MvPolynomial (Fin n) (ZMod 2)) (hmlf : IsMultilinear f) (hdegf : f.totalDegree≤k)
    (hfB : f∈Ble (Fin n) B) (hRf : R ⟨f,hfB⟩≠0)
    (Cl : ACirc (ZMod 2) (Fin n) → Prop) (π : List (ACirc (ZMod 2) (Fin n)))
    (hπ : IsSemPCRef Cl Set.univ (polyAx F) π)
    (hdegree : ∀ c∈π, (multiplied f c).totalDegree≤D) : False := by
  have hDB : D≤B := by omega
  have hFB : ∀ a∈F, a∈Ble (Fin n) B := by
    intro a ha
    exact (mem_Ble_iff B a).mpr ⟨(hF a ha).1,by have hh := (hF a ha).2; omega⟩
  have hBle : ∀ c∈π, multiplied f c∈Ble (Fin n) B := by
    intro c hc
    exact (mem_Ble_iff B _).mpr ⟨ml_multilinear _,(hdegree c hc).trans hDB⟩
  have hz : ∀ i (hi : i<π.length), R ⟨multiplied f π[i],hBle _ (List.getElem_mem hi)⟩=0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      rcases hπ.2.1 i hi with ⟨a,ha,he⟩ | he | ⟨j,l,hj,hl,he⟩
      · obtain ⟨a,ha,rfl⟩ := ha
        have hp : ML (a*f)∈Ble (Fin n) B := (mem_Ble_iff B _).mpr ⟨ml_multilinear _,by
          apply (AC02Frege.P2MBooleanFlip.ml_totalDegree_le _).trans
          apply (totalDegree_mul _ _).trans
          have hh := (hF a ha).2
          omega⟩
        have heq : multiplied f π[i]=ML (a*f) := by
          apply polyFn_ext (ml_multilinear _) (ml_multilinear _)
          intro x
          change polyFn (multiplied f π[i]) x=polyFn (ML (a*f)) x
          rw [multiplied_value,he x (Set.mem_univ x)]
          simp only [polyFn,eval_ml,map_mul]
          ring
        have hsub : (⟨multiplied f π[i],hBle _ (List.getElem_mem hi)⟩ : Ble (Fin n) B)=⟨ML (a*f),hp⟩ :=
          Subtype.ext heq
        rw [hsub]
        exact axiom_product F R hR hFB a f ha (by have hh := (hF a ha).2; omega) hp
      · have heq : multiplied f π[i]=0 := by
          apply polyFn_ext (ml_multilinear _) (by intro s hs; simp at hs)
          intro x
          change polyFn (multiplied f π[i]) x=polyFn (0 : MvPolynomial (Fin n) (ZMod 2)) x
          rw [multiplied_value,he x (Set.mem_univ x)]
          simp [polyFn]
        have hsub : (⟨multiplied f π[i],hBle _ (List.getElem_mem hi)⟩ : Ble (Fin n) B)=0 := Subtype.ext heq
        rw [hsub,map_zero]
      · apply P2MPseudoReductionSemanticClosure.binary F R hR hB
          (multiplied f π[j]) (multiplied f π[l]) (multiplied f π[i])
          (hBle _ (List.getElem_mem (hj.trans hi))) (hBle _ (List.getElem_mem (hl.trans hi))) _
          (hdegree _ (List.getElem_mem (hj.trans hi))) (hdegree _ (List.getElem_mem (hl.trans hi)))
          (hdegree _ (List.getElem_mem hi)) (ih j hj (hj.trans hi)) (ih l hl (hl.trans hi))
        intro x h₁ h₂
        rcases P2MMajorityFoundation.eq_zero_or_one (polyFn f x) with hf | hf
        · simp only [multiplied_value,hf,zero_mul]
        · have hp : cval π[j] x=0 := by simpa only [multiplied_value,hf,one_mul] using h₁
          have hq : cval π[l] x=0 := by simpa only [multiplied_value,hf,one_mul] using h₂
          simpa only [multiplied_value,hf,one_mul] using he x (Set.mem_univ x) hp hq
  obtain ⟨c,hc,hval⟩ := hπ.2.2
  have hmem := List.mem_of_getLast? hc
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hmem
  have heq : multiplied f π[i]=f := by
    apply polyFn_ext (ml_multilinear _) hmlf
    intro x
    change polyFn (multiplied f π[i]) x=polyFn f x
    rw [multiplied_value,he,hval x (Set.mem_univ x),mul_one]
  have hsub : (⟨multiplied f π[i],hBle _ (List.getElem_mem hi)⟩ : Ble (Fin n) B)=⟨f,hfB⟩ := Subtype.ext heq
  have hh := hz i hi
  rw [hsub] at hh
  exact hRf hh

end SemAC02.Supplement.P2MSPSCommonMultiplierSoundness
end

section
-- Inlined Solutions.P2MPseudoReductionRestriction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPseudoReductionRestriction

open P2MBooleanDegreeSpaces

lemma ble_mono {V : Type} {k B : ℕ} (h : k≤B) : Ble V k≤Ble V B := by
  intro p hp
  exact (mem_Ble_iff B p).mpr ⟨((mem_Ble_iff k p).mp hp).1,((mem_Ble_iff k p).mp hp).2.trans h⟩

noncomputable def restricted {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) : Ble V k →ₗ[ZMod 2] W :=
  R.comp (Submodule.inclusion (ble_mono hk))

theorem range_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    LinearMap.range (restricted R k hk)=((Submodule.comap (Ble V B).subtype (Ble V k)).map R) := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨Submodule.inclusion (ble_mono hk) p,p.2,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩

theorem rank_eq {V : Type} {B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble V B →ₗ[ZMod 2] W) (k : ℕ) (hk : k≤B) :
    Module.finrank (ZMod 2) (LinearMap.range (restricted R k hk))=rankLe R k := by
  rw [range_eq]
  rfl

end SemAC02.Supplement.P2MPseudoReductionRestriction
end

section
-- Inlined Solutions.P2MSPSSizeBound

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSPSSizeBound

open MvPolynomial ACirc AC02Frege P2MBooleanDegreeSpaces

theorem size_bound {n : ℕ} (F : Set (MvPolynomial (Fin n) (ZMod 2))) (d₀ : ℕ)
    (hF : ∀ f∈F, IsMultilinear f ∧ f.totalDegree ≤ d₀)
    (k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hB : 3*(k+max d₀ r) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble (Fin n) (3*(k+max d₀ r)) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (π : List (ACirc (ZMod 2) (Fin n))) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    (rankLe R k : ℝ)/(2*((n-r).choose k : ℝ)) ≤ topS Set.univ π := by
  classical
  let D := k+max d₀ r
  have hkB : k ≤ 3*D := by dsimp [D]; omega
  have hkr : 3*k ≤ n-r := by
    have hm : r ≤ max d₀ r := le_max_right _ _
    omega
  have hchoose : 0 < (n-r).choose k := Nat.choose_pos (by omega)
  have hden : (0 : ℝ) < 2*((n-r).choose k : ℝ) := by exact_mod_cast (show 0 < 2*(n-r).choose k by omega)
  by_contra hnot
  have hsmall := (lt_div_iff₀ hden).mp (lt_of_not_ge hnot)
  have hgt : 2*(n-r).choose k*topS Set.univ π < rankLe R k := by
    exact_mod_cast (show (2 : ℝ)*((n-r).choose k : ℝ)*(topS Set.univ π : ℝ) < rankLe R k by nlinarith)
  let E := P2MSPSTopPolynomials.pool π
  let models (T : E) : P2MSPSTermData.Model n k T.1 :=
    Classical.choice (P2MSPSTopPolynomials.model_exists π hπ.1 k T.1 T.2)
  let Rk := P2MPseudoReductionRestriction.restricted R k hkB
  have hcard := P2MSPSTopPolynomials.card_le_topS π
  have hrank : 2*(n-r).choose k*E.card < Module.finrank (ZMod 2) Rk.range := by
    rw [P2MPseudoReductionRestriction.rank_eq]
    exact (Nat.mul_le_mul_left (2*(n-r).choose k) hcard).trans_lt hgt
  obtain ⟨f,hfR,hkill⟩ := P2MSPSCommonMultiplierExistence.exists_multiplier E models Rk hkr hrank
  have hfB : (f : MvPolynomial (Fin n) (ZMod 2))∈Ble (Fin n) (3*D) :=
    P2MPseudoReductionRestriction.ble_mono hkB f.2
  have hfR' : R ⟨(f : MvPolynomial (Fin n) (ZMod 2)),hfB⟩≠0 := hfR
  obtain ⟨hmlf,hdf⟩ := (mem_Ble_iff k (f : MvPolynomial (Fin n) (ZMod 2))).mp f.2
  have hdegree := P2MSPSLineMultiplierDegree.proof_degree π hπ.1 f hkill
  apply P2MSPSCommonMultiplierSoundness.no_annihilator F hF R hR (by omega : 3*D ≤ 3*D)
    (by dsimp [D]; omega) f hmlf hdf hfB hfR' IsSPS π hπ
  intro c hc
  exact (hdegree c hc).trans (by dsimp [D]; omega)

end SemAC02.Supplement.P2MSPSSizeBound
end

end P2MSPSSizeBoundProof
open SemAC02.Supplement SemAC02.Supplement.ACirc MvPolynomial

theorem solution {n : ℕ} (F : Set (MvPolynomial (Fin n) (ZMod 2))) (d₀ : ℕ)
    (hF : ∀ f ∈ F, AC02Frege.IsMultilinear f ∧ f.totalDegree ≤ d₀)
    (k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hB : 3 * (k + max d₀ r) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble (Fin n) (3 * (k + max d₀ r)) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (π : List (ACirc (ZMod 2) (Fin n))) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    (rankLe R k : ℝ) / (2 * ((n - r).choose k : ℝ)) ≤ topS Set.univ π  := by
  exact P2MSPSSizeBoundProof.SemAC02.Supplement.P2MSPSSizeBound.size_bound F d₀ hF k r hk hkn hr hrn hB R hR π hπ
