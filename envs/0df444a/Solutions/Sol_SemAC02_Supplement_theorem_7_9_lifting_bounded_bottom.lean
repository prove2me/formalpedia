-- Prove2me | solution 1 for SemAC02.Supplement.theorem_7_9_lifting_bounded_bottom
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T08:40:16.864841+00:00
-- url     : https://prove2.me/submissions/7b8ff7aa-95b9-42f8-a759-aa9ec96af177

import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Supplement_selLift
import Definitions.Def_SemAC02_Supplement_clauseAx
import Mathlib
import Definitions.Def_SemAC02_Supplement_IsSemPCRef

open _root_.SemAC02 _root_.SemAC02.Supplement _root_.SemAC02.Supplement.ACirc
open _root_.AC02Frege
namespace P2MSelectorBoundedBottomProof
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
-- Inlined Solutions.P2MBooleanFieldPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanFieldPolynomials

open MvPolynomial

lemma bool_power {F V : Type} [CommRing F] (x : V → Bool) (i : V) (a : ℕ) :
    (boolPt x i : F)^min a 1=(boolPt x i : F)^a := by
  cases h : x i <;> cases a <;> simp [boolPt,h]

theorem value_mlz {F V : Type} [CommRing F] (p : MvPolynomial V F) : polyFn (mlz p)=polyFn p := by
  classical
  funext x
  change eval (boolPt x) (mlz p)=eval (boolPt x) p
  rw [mlz,map_sum]
  conv_rhs => rw [p.as_sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [eval_monomial,eval_monomial]
  congr 1
  simp only [Finsupp.prod,AC02Frege.P2MBooleanAlgebra.sqfree_support]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [AC02Frege.sqfree,Finsupp.mapRange_apply] using bool_power (F:=F) x i (s i)

lemma monomial_value {F V : Type} [CommRing F] (s : V →₀ ℕ) (a : F) (x : V → Bool) :
    polyFn (monomial s a) x=a*∏ i∈s.support, (boolPt x i : F) := by
  classical
  rw [polyFn,eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have he : s i≠0 := Finsupp.mem_support_iff.mp hi
  cases h : x i <;> simp [boolPt,h,he]

end SemAC02.Supplement.P2MBooleanFieldPolynomials
end

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
-- Inlined Solutions.P2MPolynomialArithmeticCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPolynomialArithmeticCircuits

open MvPolynomial ACirc P2MArithmeticCircuitBasics

noncomputable def factors {F V : Type} (s : V →₀ ℕ) : List (ACirc F V) :=
  s.support.toList.flatMap (fun i => List.replicate (s i) (.var i))

noncomputable def monomialCircuit {F V : Type} (s : V →₀ ℕ) : ACirc F V := .prod (factors s)

noncomputable def polynomialCircuit {F V : Type} [CommRing F] (p : MvPolynomial V F) : ACirc F V :=
  .sum (p.support.toList.map (fun s => (coeff s p,monomialCircuit s)))

lemma factors_length {F V : Type} (s : V →₀ ℕ) : (factors (F:=F) s).length=s.sum (fun _ e => e) := by
  simp [factors,List.length_flatMap,Finsupp.sum,Finset.sum_toList]

lemma factors_leaves {F V : Type} (s : V →₀ ℕ) : ∀ c∈factors (F:=F) s, IsLeaf c := by
  intro c hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp hc
  trivial

theorem monomial_layer {F V : Type} (s : V →₀ ℕ) (D : ℕ) (hs : s.sum (fun _ e => e) ≤ D) :
    IsMonGate (D : ℕ∞) (monomialCircuit (F:=F) s) := by
  constructor
  · rw [factors_length]
    exact_mod_cast hs
  · exact factors_leaves s

theorem monomial_poly {F V : Type} [CommRing F] (s : V →₀ ℕ) :
    (monomialCircuit (F:=F) s).toPoly=monomial s 1 := by
  classical
  rw [monomialCircuit,toPoly_prod,monomial_eq, C_1,one_mul]
  simp [factors,List.map_flatMap,List.flatMap_def,List.prod_flatten,Finsupp.prod,Finset.prod_map_toList,toPoly]

theorem polynomial_poly {F V : Type} [CommRing F] (p : MvPolynomial V F) :
    (polynomialCircuit p).toPoly=p := by
  rw [polynomialCircuit,toPoly_sum]
  simp only [List.map_map,Function.comp_def,monomial_poly,C_mul_monomial,mul_one]
  rw [Finset.sum_map_toList]
  exact support_sum_monomial_coeff p

theorem polynomial_layer {F V : Type} [CommRing F] (p : MvPolynomial V F) (D : ℕ)
    (hp : p.totalDegree ≤ D) : IsSumOf (IsMonGate (D : ℕ∞)) (polynomialCircuit p) := by
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  exact monomial_layer s D ((le_totalDegree (Finset.mem_toList.mp hs)).trans hp)

end SemAC02.Supplement.P2MPolynomialArithmeticCircuits
end

section
-- Inlined Solutions.P2MFieldSelectorProjection

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorProjection

open MvPolynomial

variable {F V : Type} [Field F] {q : ℕ}

def liftPoint (A : (V×Bool) → Fin q) (x : V → Bool) (z : V×Bool×Fin q) : Bool :=
  if z.2.2=A (z.1,z.2.1) then if z.2.1 then x z.1 else !(x z.1) else false

noncomputable def rho (A : (V×Bool) → Fin q) (z : V×Bool×Fin q) : MvPolynomial V F :=
  if z.2.2=A (z.1,z.2.1) then if z.2.1 then X z.1 else 1-X z.1 else 0

lemma rho_degree (A : (V×Bool) → Fin q) (z : V×Bool×Fin q) : (rho (F:=F) A z).totalDegree ≤ 1 := by
  unfold rho
  split_ifs <;> try simp
  exact (totalDegree_sub _ _).trans (by simp)

lemma rho_value (A : (V×Bool) → Fin q) (x : V → Bool) (z : V×Bool×Fin q) :
    eval (boolPt x) (rho (F:=F) A z)=boolPt (liftPoint A x) z := by
  by_cases h : z.2.2=A (z.1,z.2.1)
  · cases hb : z.2.1 <;> cases hx : x z.1 <;> simp [rho,liftPoint,h,hb,boolPt,hx]
  · simp [rho,liftPoint,h,boolPt]

lemma pair_zero (A : (V×Bool) → Fin q) (x : V → Bool) (z z' : V×Bool×Fin q)
    (hb : z.1=z'.1) (hne : z≠z') :
    (boolPt (liftPoint A x) z : F)=0 ∨ (boolPt (liftPoint A x) z' : F)=0 := by
  by_cases hz : z.2.2=A (z.1,z.2.1)
  · by_cases hz' : z'.2.2=A (z'.1,z'.2.1)
    · have hr : z.2.1≠z'.2.1 := by
        intro he
        apply hne
        apply Prod.ext hb
        apply Prod.ext he
        rw [hz,hz',hb,he]
      rcases z with ⟨i,b,a⟩
      rcases z' with ⟨j,b',a'⟩
      dsimp only at hb hr hz hz' ⊢
      subst j
      cases hx : x i <;> cases b <;> cases b' <;> simp_all [liftPoint,boolPt]
    · exact Or.inr (by simp [liftPoint,hz',boolPt])
  · exact Or.inl (by simp [liftPoint,hz,boolPt])

def Alive (s : (V×Bool×Fin q) →₀ ℕ) (A : (V×Bool) → Fin q) : Prop :=
  (∀ z∈s.support, z.2.2=A (z.1,z.2.1)) ∧
    Set.InjOn (fun z : V×Bool×Fin q => z.1) (s.support : Set (V×Bool×Fin q))

lemma killed (s : (V×Bool×Fin q) →₀ ℕ) (A : (V×Bool) → Fin q) (hdead : ¬ Alive s A)
    (x : V → Bool) : (∏ z∈s.support, (boolPt (liftPoint A x) z : F))=0 := by
  classical
  by_cases hcols : ∀ z∈s.support, z.2.2=A (z.1,z.2.1)
  · have hni : ¬ Set.InjOn (fun z : V×Bool×Fin q => z.1) (s.support : Set (V×Bool×Fin q)) :=
      fun hi => hdead ⟨hcols,hi⟩
    simp only [Set.InjOn,Finset.mem_coe,not_forall,_root_.not_imp] at hni
    obtain ⟨z,hz,z',hz',hb,hne⟩ := hni
    rcases pair_zero (F:=F) A x z z' hb hne with hzero | hzero
    · exact Finset.prod_eq_zero hz hzero
    · exact Finset.prod_eq_zero hz' hzero
  · push_neg at hcols
    obtain ⟨z,hz,hcol⟩ := hcols
    apply Finset.prod_eq_zero hz
    simp [liftPoint,hcol,boolPt]

noncomputable def project [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F) : MvPolynomial V F :=
  ∑ s∈(mlz p).support.filter (fun s => s.support.card ≤ d),
    C (coeff s (mlz p))*∏ z∈s.support, rho A z

theorem project_degree [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F) : (project A d p).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _z∈s.support, 1 := Finset.sum_le_sum (fun z hz => rho_degree A z)
    _ = s.support.card := by simp
    _ ≤ d := (Finset.mem_filter.mp hs).2

theorem project_value [DecidableEq V] (A : (V×Bool) → Fin q) (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) F)
    (hgood : ∀ s∈(mlz p).support, d < s.support.card → ¬ Alive s A) (x : V → Bool) :
    polyFn (project A d p) x=polyFn p (liftPoint A x) := by
  classical
  rw [←P2MBooleanFieldPolynomials.value_mlz p]
  change eval (boolPt x) (project A d p)=polyFn (mlz p) (liftPoint A x)
  rw [project,map_sum]
  conv_rhs => rw [(mlz p).as_sum]
  simp only [polyFn,map_sum,P2MBooleanFieldPolynomials.monomial_value]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show eval (boolPt (liftPoint A x)) (monomial s (coeff s (mlz p)))=
      coeff s (mlz p)*∏ z∈s.support, (boolPt (liftPoint A x) z : F) from
    P2MBooleanFieldPolynomials.monomial_value s (coeff s (mlz p)) (liftPoint A x)]
  by_cases hsmall : s.support.card ≤ d
  · simp only [if_pos hsmall,map_mul,eval_C,map_prod,rho_value]
  · simp only [if_neg hsmall]
    rw [killed s A (hgood s hs (by omega)) x,mul_zero]

end SemAC02.Supplement.P2MFieldSelectorProjection
end

section
-- Inlined Solutions.P2MFieldSelectorCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorCircuits

open MvPolynomial ACirc P2MArithmeticCircuitBasics P2MPolynomialArithmeticCircuits P2MFieldSelectorProjection

variable {F V : Type} [Field F] [DecidableEq V] {q : ℕ}

noncomputable def bottom (A : (V×Bool) → Fin q) (d : ℕ) (c : ACirc F (V×Bool×Fin q)) : ACirc F V :=
  polynomialCircuit (project A d c.toPoly)

noncomputable def term (A : (V×Bool) → Fin q) (d : ℕ) : ACirc F (V×Bool×Fin q) → ACirc F V
  | .prod cs => .prod (cs.map (bottom A d))
  | _ => .prod []

noncomputable def line (A : (V×Bool) → Fin q) (d : ℕ) : ACirc F (V×Bool×Fin q) → ACirc F V
  | .sum ps => .sum (ps.map (fun p => (p.1,term A d p.2)))
  | _ => .sum []

theorem term_layer (A : (V×Bool) → Fin q) (d : ℕ) (t : ACirc F (V×Bool×Fin q)) :
    IsProdOf (IsSumOf (IsMonGate (d : ℕ∞))) (term A d t) := by
  cases t <;> try exact fun c hc => (List.not_mem_nil hc).elim
  case prod cs =>
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    exact polynomial_layer _ d (project_degree A d b.toPoly)

theorem line_layer (A : (V×Bool) → Fin q) (d : ℕ) (c : ACirc F (V×Bool×Fin q)) :
    IsSPSP (d : ℕ∞) (line A d c) := by
  cases c <;> try exact fun p hp => (List.not_mem_nil hp).elim
  case sum ps =>
    intro p hp
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
    exact term_layer A d z.2

theorem prod_value (A : (V×Bool) → Fin q) (d : ℕ) (cs : List (ACirc F (V×Bool×Fin q)))
    (hgood : ∀ b∈cs, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive s A) (x : V → Bool) :
    cval (term A d (.prod cs)) x=cval (.prod cs) (liftPoint A x) := by
  simp only [term,cval_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b hb
  change polyFn (polynomialCircuit (project A d b.toPoly)).toPoly x=cval b (liftPoint A x)
  rw [polynomial_poly]
  exact project_value A d b.toPoly (hgood b hb) x

theorem line_value (A : (V×Bool) → Fin q) (d : ℕ) (c : ACirc F (V×Bool×Fin q))
    (hc : IsSPSP ⊤ c)
    (hgood : ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive s A)
    (x : V → Bool) : cval (line A d c) x=cval c (liftPoint A x) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    simp only [line,cval_sum,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    have hterm := hc p hp
    cases ht : p.2 with
    | var i => simp only [ht,IsProdOf] at hterm
    | const a => simp only [ht,IsProdOf] at hterm
    | sum qs => simp only [ht,IsProdOf] at hterm
    | prod cs =>
      apply prod_value
      intro b hb s hs hbig
      apply hgood b _ s hs hbig
      exact List.mem_flatMap.mpr ⟨p,hp,by simp only [ht]; exact hb⟩

theorem top_terms (A : (V×Bool) → Fin q) (d : ℕ) (c : ACirc F (V×Bool×Fin q)) :
    topTerms (line A d c)=(topTerms c).map (term A d) := by
  cases c <;> simp [line,topTerms,List.map_map,Function.comp_def]

theorem term_value (A : (V×Bool) → Fin q) (d : ℕ) (c t : ACirc F (V×Bool×Fin q))
    (hc : IsSPSP ⊤ c) (ht : t∈topTerms c)
    (hgood : ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive s A)
    (x : V → Bool) : cval (term A d t) x=cval t (liftPoint A x) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    have hterm := hc p hp
    cases ht : p.2 with
    | var i => simp only [ht,IsProdOf] at hterm
    | const a => simp only [ht,IsProdOf] at hterm
    | sum qs => simp only [ht,IsProdOf] at hterm
    | prod cs =>
      apply prod_value
      intro b hb s hs hbig
      apply hgood b _ s hs hbig
      exact List.mem_flatMap.mpr ⟨p,hp,by simp only [ht]; exact hb⟩

end SemAC02.Supplement.P2MFieldSelectorCircuits
end

section
-- Inlined Solutions.P2MFieldSelectorClauseProjection

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorClauseProjection

open MvPolynomial LiftSAParity P2MFieldSelectorProjection Classical

lemma literal_value {F V : Type} [Field F] (l : V×Bool) (x : V → Bool) :
    polyFn (litPolyF (F:=F) l) x=if x l.1=l.2 then 0 else 1 := by
  cases hb : l.2 <;> cases hx : x l.1 <;> simp [polyFn,litPolyF,boolPt,hb,hx]

theorem clause_value {F V : Type} [Field F] (C : Clause V) (x : V → Bool) :
    polyFn (clausePolyF (F:=F) C) x=if Falsifies x C then 1 else 0 := by
  classical
  change eval (boolPt x) (∏ l∈C, litPolyF l)=_
  rw [map_prod]
  by_cases hf : Falsifies x C
  · rw [if_pos hf]
    apply Finset.prod_eq_one
    intro l hl
    exact (literal_value (F:=F) l x).trans (if_neg (hf l hl))
  · rw [if_neg hf]
    unfold Falsifies at hf
    push_neg at hf
    obtain ⟨l,hl,he⟩ := hf
    apply Finset.prod_eq_zero hl
    exact (literal_value (F:=F) l x).trans (if_pos he)

lemma lifted_falsifies {V : Type} [DecidableEq V] {q : ℕ}
    (A : (V×Bool) → Fin q) (C : Clause V) (x : V → Bool) :
    Falsifies (liftPoint A x) (C.biUnion (fun l =>
      Finset.univ.image (fun a : Fin q => ((l.1,l.2,a),true)))) ↔ Falsifies x C := by
  constructor
  · intro h l hl
    have hh := h ((l.1,l.2,A (l.1,l.2)),true)
      (Finset.mem_biUnion.mpr ⟨l,hl,Finset.mem_image.mpr ⟨A (l.1,l.2),Finset.mem_univ _,rfl⟩⟩)
    cases hb : l.2 <;> cases hx : x l.1 <;> simp_all [liftPoint]
  · intro h z hz
    obtain ⟨l,hl,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hh := h l hl
    by_cases hcol : a=A (l.1,l.2)
    · cases hb : l.2 <;> cases hx : x l.1 <;> simp_all [liftPoint]
    · simp [liftPoint,hcol]

lemma selector_satisfied {V : Type} [DecidableEq V] {q : ℕ} (A : (V×Bool) → Fin q) (i : V) (x : V → Bool) :
    ¬ Falsifies (liftPoint A x) (Finset.univ.image (fun c : Bool×Fin q => ((i,c),true))) := by
  intro hf
  have hh := hf ((i,x i,A (i,x i)),true)
    (Finset.mem_image.mpr ⟨(x i,A (i,x i)),Finset.mem_univ _,rfl⟩)
  cases hx : x i <;> simp_all [liftPoint]

lemma exclusion_satisfied {F V : Type} [Field F] [DecidableEq V] {q : ℕ} (A : (V×Bool) → Fin q) (i : V)
    (S : Finset (Bool×Fin q)) (hS : S.card=2) (x : V → Bool) :
    ¬ Falsifies (liftPoint A x) (S.image (fun c => ((i,c),false))) := by
  classical
  intro hf
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  have ha := hf ((i,a),false) (Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
  have hb := hf ((i,b),false) (Finset.mem_image.mpr ⟨b,by simp,rfl⟩)
  have ha' : liftPoint A x (i,a)=true := Bool.eq_true_of_not_eq_false ha
  have hb' : liftPoint A x (i,b)=true := Bool.eq_true_of_not_eq_false hb
  rcases pair_zero (F:=F) A x (i,a) (i,b) rfl (by intro he; exact hab (Prod.mk.inj he).2) with h | h
  · exact one_ne_zero (by simpa only [boolPt,ha',↓reduceIte] using h)
  · exact one_ne_zero (by simpa only [boolPt,hb',↓reduceIte] using h)

theorem input_projection {F : Type} [Field F] {n q : ℕ} (A : (Fin n×Bool) → Fin q)
    (base : List (Clause (Fin n))) (C : Clause (Fin n×Bool×Fin q)) (hC : C∈selLift q base) :
    (∃ D∈base, ∀ x, polyFn (clausePolyF (F:=F) C) (liftPoint A x)=polyFn (clausePolyF D) x) ∨
      (∀ x, polyFn (clausePolyF (F:=F) C) (liftPoint A x)=0) := by
  classical
  simp only [selLift,List.mem_append,List.mem_map,List.mem_flatMap] at hC
  rcases hC with (⟨i,hi,rfl⟩ | ⟨i,hi,S,hS,rfl⟩) | ⟨D,hD,rfl⟩
  · right
    intro x
    simp only [clause_value,if_neg (selector_satisfied A i x)]
  · right
    intro x
    have hcard : S.card=2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hS)).2
    simp only [clause_value,if_neg (exclusion_satisfied (F:=F) A i S hcard x)]
  · left
    refine ⟨D,hD,?_⟩
    intro x
    rw [clause_value,clause_value,lifted_falsifies]

end SemAC02.Supplement.P2MFieldSelectorClauseProjection
end

section
-- Inlined Solutions.P2MFinitePinningCount

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MFinitePinningCount

noncomputable def restrictionEquiv {I A : Type} [DecidableEq I]
    (S : Finset I) (f : I → A) :
    {g : I → A // ∀ i∈S, g i=f i} ≃ ({i : I // i∉S} → A) where
  toFun g i := g.1 i.1
  invFun h := ⟨fun i => if hi : i∈S then f i else h ⟨i,hi⟩, by
    intro i hi
    simp only [dif_pos hi]⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    by_cases hi : i∈S
    · simp only [dif_pos hi]
      exact (g.2 i hi).symm
    · simp only [dif_neg hi]
  right_inv h := by
    funext i
    simp only [dif_neg i.2]

theorem pinned_card {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) :
    Fintype.card {g : I → A // ∀ i∈S, g i=f i} =
      Fintype.card A^(Fintype.card I-S.card) := by
  classical
  rw [Fintype.card_congr (restrictionEquiv S f),Fintype.card_fun]
  congr 1
  have he : (Finset.univ.filter (fun i : I => i∉S))=Finset.univ\S := by ext i; simp
  rw [Fintype.card_subtype,he,Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]

theorem filter_card {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) :
    ((Finset.univ : Finset (I → A)).filter (fun (g : I → A) => ∀ i∈S, g i=f i)).card =
      Fintype.card A^(Fintype.card I-S.card) := by
  classical
  rw [← Fintype.card_subtype]
  exact pinned_card S f

theorem probability_bound {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) (d : ℕ) (hd : d≤S.card) (hA : 1≤Fintype.card A) :
    (((Finset.univ : Finset (I → A)).filter (fun (g : I → A) => ∀ i∈S, g i=f i)).card : ℝ) ≤
      (Fintype.card A : ℝ)^(Fintype.card I)/(Fintype.card A : ℝ)^d := by
  classical
  rw [filter_card]
  have hS : S.card≤Fintype.card I := Finset.card_le_univ S
  have hle : Fintype.card I-S.card≤Fintype.card I-d := by omega
  have hApos : (0 : ℝ)<(Fintype.card A : ℝ) := by exact_mod_cast (show 0<Fintype.card A by omega)
  have hAone : (1 : ℝ)≤(Fintype.card A : ℝ) := by exact_mod_cast hA
  push_cast
  calc
    _ ≤ (Fintype.card A : ℝ)^(Fintype.card I-d) := pow_le_pow_right₀ hAone hle
    _ = _ := by rw [pow_sub₀ (Fintype.card A : ℝ) hApos.ne' (by omega : d≤Fintype.card I),div_eq_mul_inv]

end ProofComplexity.P2MFinitePinningCount
end

section
-- Inlined Solutions.P2MFieldSelectorCounting

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorCounting

open MvPolynomial P2MFieldSelectorProjection Classical

noncomputable def rows {V : Type} [DecidableEq V] {q : ℕ}
    (s : (V×Bool×Fin q) →₀ ℕ) : Finset (V×Bool) := s.support.image (fun z => (z.1,z.2.1))

lemma rows_card {V : Type} [DecidableEq V] {q : ℕ} (s : (V×Bool×Fin q) →₀ ℕ)
    (A : (V×Bool) → Fin q) (h : Alive s A) : (rows s).card=s.support.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  exact h.2 hx hy (congrArg (fun z : V×Bool => z.1) he)

noncomputable def bad {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (d : ℕ) (s : (V×Bool×Fin q) →₀ ℕ) : Finset ((V×Bool) → Fin q) :=
  Finset.univ.filter (fun A => d < s.support.card ∧ Alive s A)

theorem bad_card {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2 ≤ q)
    (d : ℕ) (s : (V×Bool×Fin q) →₀ ℕ) :
    ((bad d s).card : ℝ) ≤ (q : ℝ)^(2*Fintype.card V)/(q : ℝ)^(d+1) := by
  by_cases hsome : ∃ A, A∈bad d s
  · obtain ⟨A₀,hA₀⟩ := hsome
    obtain ⟨hbig,hAlive₀⟩ := (Finset.mem_filter.mp hA₀).2
    have hrows : d+1 ≤ (rows s).card := by rw [rows_card s A₀ hAlive₀]; omega
    have hsub : bad d s⊆Finset.univ.filter (fun A : (V×Bool) → Fin q => ∀ i∈rows s, A i=A₀ i) := by
      intro A hA
      obtain ⟨_,hAlive⟩ := (Finset.mem_filter.mp hA).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro i hi
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
      exact (hAlive.1 z hz).symm.trans (hAlive₀.1 z hz)
    have hpin := ProofComplexity.P2MFinitePinningCount.probability_bound (rows s) A₀ (d+1) hrows
      (by simpa using (show 1 ≤ q by omega) : 1 ≤ Fintype.card (Fin q))
    have hcard : ((bad d s).card : ℝ) ≤
        ((Finset.univ.filter (fun A : (V×Bool) → Fin q => ∀ i∈rows s, A i=A₀ i)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.mul_comm] using hcard.trans hpin
  · have he : bad d s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact hsome ⟨A,hA⟩
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem exists_good {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2 ≤ q)
    (E : Finset ((V×Bool×Fin q) →₀ ℕ)) (d : ℕ) (hsize : E.card < q^(d+1)) :
    ∃ A : (V×Bool) → Fin q, ∀ s∈E, d < s.support.card → ¬ Alive s A := by
  let Bad := E.biUnion (bad d)
  have hc : (Bad.card : ℝ) ≤ (E.card : ℝ)*((q : ℝ)^(2*Fintype.card V)/(q : ℝ)^(d+1)) := by
    calc
      _ ≤ ((∑ s∈E, (bad d s).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = ∑ s∈E, ((bad d s).card : ℝ) := by simp
      _ ≤ ∑ _s∈E, (q : ℝ)^(2*Fintype.card V)/(q : ℝ)^(d+1) :=
        Finset.sum_le_sum (fun s hs => bad_card hq d s)
      _ = _ := by simp
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hsR : (E.card : ℝ) < (q : ℝ)^(d+1) := by exact_mod_cast hsize
  have hstrict : (Bad.card : ℝ) < (q : ℝ)^(2*Fintype.card V) := by
    apply hc.trans_lt
    have hp := pow_pos hqR (2*Fintype.card V)
    have hd := pow_pos hqR (d+1)
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have hnat : Bad.card < (Finset.univ : Finset ((V×Bool) → Fin q)).card := by
    have hcard : (Finset.univ : Finset ((V×Bool) → Fin q)).card=q^(2*Fintype.card V) := by
      simp [Fintype.card_fun,Fintype.card_prod,Nat.mul_comm]
    rw [hcard]
    exact_mod_cast hstrict
  obtain ⟨A,hA,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hnat
  refine ⟨A,?_⟩
  intro s hs hbig hAlive
  exact hnot (Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbig,hAlive⟩⟩)

end SemAC02.Supplement.P2MFieldSelectorCounting
end

section
-- Inlined Solutions.P2MProofTopFunctions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MProofTopFunctions

open ACirc Classical

noncomputable def pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    Finset (Ω → F) :=
  ((π.flatMap topTerms).map (fun t => fun x : Ω => cval t x.1)).toFinset.filter (fun g => g≠0)

theorem mem_pool {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) (g : Ω → F) :
    g∈pool Ω π ↔ g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, (fun x : Ω => cval t x.1)=g := by
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
    obtain ⟨c,hc,ht⟩ := List.mem_flatMap.mp ht
    exact ⟨hn,c,hc,t,ht,he⟩
  · rintro ⟨hn,c,hc,t,ht,he⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨t,List.mem_flatMap.mpr ⟨c,hc,ht⟩,he⟩),hn⟩

theorem card_eq_topS {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    (pool Ω π).card=topS Ω π := by
  have he : {g : Ω → F | g≠0 ∧ ∃ c∈π, ∃ t∈topTerms c, g=fun x => cval t x.1}=
      (↑(pool Ω π) : Set (Ω → F)) := by
    ext g
    rw [Finset.mem_coe,mem_pool]
    constructor
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
    · rintro ⟨hn,c,hc,t,ht,he⟩; exact ⟨hn,c,hc,t,ht,he.symm⟩
  unfold topS
  rw [he,Set.ncard_coe_finset]

theorem projection_bound {F V U : Type} [CommRing F]
    (η : (U → Bool) → (V → Bool)) (M τ : ACirc F V → ACirc F U)
    (π : List (ACirc F V))
    (hterms : ∀ c, topTerms (M c)=(topTerms c).map τ)
    (hval : ∀ c∈π, ∀ t∈topTerms c, ∀ y, cval (τ t) y=cval t (η y)) :
    topS Set.univ (π.map M) ≤ topS Set.univ π := by
  let pull (f : ↥(Set.univ : Set (V → Bool)) → F) : ↥(Set.univ : Set (U → Bool)) → F :=
    fun y => f ⟨η y.1,Set.mem_univ _⟩
  have hsub : pool Set.univ (π.map M)⊆(pool Set.univ π).image pull := by
    intro g hg
    obtain ⟨hn,c',hc',t',ht',he⟩ := (mem_pool Set.univ (π.map M) g).mp hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hc'
    rw [hterms c] at ht'
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht'
    let f : ↥(Set.univ : Set (V → Bool)) → F := fun x => cval t x.1
    have hpull : pull f=g := by
      rw [←he]
      funext y
      exact (hval c hc t ht y.1).symm
    have hf : f≠0 := by
      intro hz
      apply hn
      rw [←hpull,hz]
      rfl
    exact Finset.mem_image.mpr ⟨f,(mem_pool Set.univ π f).mpr ⟨hf,c,hc,t,ht,rfl⟩,hpull⟩
  rw [←card_eq_topS,←card_eq_topS]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end SemAC02.Supplement.P2MProofTopFunctions
end

section
-- Inlined Solutions.P2MFieldSelectorProofProjection

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MFieldSelectorProofProjection

open MvPolynomial ACirc P2MFieldSelectorProjection P2MFieldSelectorCircuits Classical

variable {F : Type} [Field F] {n q : ℕ}

noncomputable def monomialPool (π : List (ACirc F (Fin n×Bool×Fin q))) :
    Finset ((Fin n×Bool×Fin q) →₀ ℕ) :=
  open Classical in (π.flatMap bottomPolys).toFinset.biUnion (fun b => (mlz b.toPoly).support)

def Good (π : List (ACirc F (Fin n×Bool×Fin q))) (A : (Fin n×Bool) → Fin q) (d : ℕ) : Prop :=
  ∀ c∈π, ∀ b∈bottomPolys c, ∀ s∈(mlz b.toPoly).support, d < s.support.card → ¬ Alive s A

theorem good_exists (hq : 2 ≤ q) (π : List (ACirc F (Fin n×Bool×Fin q))) (d : ℕ)
    (hsize : Mbot π < q^(d+1)) : ∃ A : (Fin n×Bool) → Fin q, Good π A d := by
  have he : Mbot π=max 1 (monomialPool π).card := by
    unfold Mbot monomialPool
    congr 2
    ext s
    simp only [Finset.mem_biUnion]
  have hE : (monomialPool π).card < q^(d+1) := by
    rw [he] at hsize
    exact (Nat.le_max_right 1 _).trans_lt hsize
  obtain ⟨A,hA⟩ := P2MFieldSelectorCounting.exists_good hq (monomialPool π) d hE
  refine ⟨A,?_⟩
  intro c hc b hb s hs hbig
  apply hA s _ hbig
  exact Finset.mem_biUnion.mpr ⟨b,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,hb⟩),hs⟩

theorem refutation (A : (Fin n×Bool) → Fin q) (d : ℕ) (base : List (LiftSAParity.Clause (Fin n)))
    (π : List (ACirc F (Fin n×Bool×Fin q)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx {C | C∈selLift q base}) π)
    (hgood : Good π A d) :
    IsSemPCRef (IsSPSP (d : ℕ∞)) Set.univ (clauseAx {C | C∈base}) (π.map (line A d)) := by
  have hvalue : ∀ c∈π, ∀ x, cval (line A d c) x=cval c (liftPoint A x) :=
    fun c hc x => line_value A d c (hπ.1 c hc) (hgood c hc) x
  refine ⟨?_,?_,?_⟩
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact line_layer A d a
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a,ha,he⟩ | he | ⟨j,l,hj,hl,he⟩
    · obtain ⟨C,hC,rfl⟩ := ha
      rcases P2MFieldSelectorClauseProjection.input_projection (F:=F) A base C hC with ⟨D,hD,hinput⟩ | hzero
      · left
        refine ⟨polyFn (clausePolyF D),⟨D,hD,rfl⟩,?_⟩
        intro x hx
        rw [hvalue _ (List.getElem_mem hi') x,he (liftPoint A x) (Set.mem_univ _),hinput x]
      · right; left
        intro x hx
        rw [hvalue _ (List.getElem_mem hi') x,he (liftPoint A x) (Set.mem_univ _),hzero x]
    · right; left
      intro x hx
      rw [hvalue _ (List.getElem_mem hi') x,he (liftPoint A x) (Set.mem_univ _)]
    · right; right
      refine ⟨j,l,hj,hl,?_⟩
      intro x hx hp hq
      rw [hvalue _ (List.getElem_mem hi') x]
      apply he (liftPoint A x) (Set.mem_univ _)
      · rwa [hvalue _ (List.getElem_mem (hj.trans hi')) x] at hp
      · rwa [hvalue _ (List.getElem_mem (hl.trans hi')) x] at hq
  · obtain ⟨c,hc,hval⟩ := hπ.2.2
    refine ⟨line A d c,?_,?_⟩
    · rw [List.getLast?_map,hc]
      rfl
    · intro x hx
      rw [hvalue c (List.mem_of_getLast? hc) x]
      exact hval (liftPoint A x) (Set.mem_univ _)

theorem size (A : (Fin n×Bool) → Fin q) (d : ℕ) (π : List (ACirc F (Fin n×Bool×Fin q)))
    (hπ : ∀ c∈π, IsSPSP ⊤ c) (hgood : Good π A d) :
    topS Set.univ (π.map (line A d)) ≤ topS Set.univ π ∧
      (π.map (line A d)).length=π.length ∧ topOcc (π.map (line A d))=topOcc π := by
  refine ⟨?_,List.length_map _,?_⟩
  · apply P2MProofTopFunctions.projection_bound (liftPoint A) (line A d) (term A d) π (top_terms A d)
    intro c hc t ht x
    exact term_value A d c t (hπ c hc) ht (hgood c hc) x
  · unfold topOcc
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [top_terms,List.length_map]

end SemAC02.Supplement.P2MFieldSelectorProofProjection
end

section
-- Inlined Solutions.P2MSelectorBoundedBottomLifting

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MSelectorBoundedBottomLifting

open ACirc P2MFieldSelectorCircuits P2MFieldSelectorProofProjection

theorem lifting {F : Type} [Field F] {n q : ℕ} (hq : 2 ≤ q)
    (base : List (LiftSAParity.Clause (Fin n))) (π : List (ACirc F (Fin n×Bool×Fin q)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx {C | C∈selLift q base}) π) :
    (∀ d : ℕ, 1 ≤ d → Mbot π < q^(d+1) →
      ∃ π' : List (ACirc F (Fin n)),
        IsSemPCRef (IsSPSP (d : ℕ∞)) Set.univ (clauseAx {C | C∈base}) π' ∧
        topS Set.univ π' ≤ topS Set.univ π ∧ π'.length ≤ π.length ∧ topOcc π' ≤ topOcc π) ∧
      Mbot π < q^(max 1 (Nat.log q (Mbot π))+1) := by
  classical
  constructor
  · intro d hd hsize
    obtain ⟨A,hgood⟩ := good_exists hq π d hsize
    have hs := size A d π hπ.1 hgood
    exact ⟨π.map (line A d),refutation A d base π hπ hgood,hs.1,hs.2.1.le,hs.2.2.le⟩
  · have hh := Nat.lt_pow_succ_log_self (by omega : 1 < q) (Mbot π)
    exact hh.trans_le (Nat.pow_le_pow_right (by omega : 0 < q)
      (Nat.add_le_add_right (Nat.le_max_right 1 _) 1))

end SemAC02.Supplement.P2MSelectorBoundedBottomLifting
end

end P2MSelectorBoundedBottomProof
open SemAC02.Supplement SemAC02.Supplement.ACirc MvPolynomial

theorem solution {𝔽 : Type} [Field 𝔽] {n q : ℕ} (hq : 2 ≤ q)
    (F : List (LiftSAParity.Clause (Fin n))) (π : List (ACirc 𝔽 (Fin n × Bool × Fin q)))
    (hπ : IsSemPCRef (IsSPSP ⊤) Set.univ
      (clauseAx {C | C ∈ selLift q F}) π) :
    (∀ d : ℕ, 1 ≤ d → Mbot π < q ^ (d + 1) →
      ∃ π' : List (ACirc 𝔽 (Fin n)),
        IsSemPCRef (IsSPSP (d : ℕ∞)) Set.univ (clauseAx {C | C ∈ F}) π' ∧
        topS Set.univ π' ≤ topS Set.univ π ∧
        π'.length ≤ π.length ∧ topOcc π' ≤ topOcc π) ∧
    Mbot π < q ^ (max 1 (Nat.log q (Mbot π)) + 1)  := by
  exact P2MSelectorBoundedBottomProof.SemAC02.Supplement.P2MSelectorBoundedBottomLifting.lifting hq F π hπ
