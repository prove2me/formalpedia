-- Prove2me | solution 1 for SemAC02.Supplement.lemma_5_3_expansion_pseudo_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T09:44:57.052217+00:00
-- url     : https://prove2.me/submissions/37d41124-cddc-4e62-86d2-e232463e02dc

import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Definitions.Def_SemAC02_Supplement_expansionRank
import Mathlib
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_SemAC02_Supplement_IsPseudoRed

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MExpansionOperatorProof
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
-- Inlined Solutions.P2MBooleanIdealMultilinearization

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MBooleanIdealMultilinearization

open MvPolynomial P2MBooleanAlgebra

lemma power_min {A : Type} [Monoid A] (x : A) (hx : x^2=x) (n : ℕ) : x^min n 1=x^n := by
  have hp : ∀ k : ℕ, x^(k+1)=x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,ih,←pow_two,hx]
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.min_eq_right (by omega : 1 ≤ n+1),pow_one] using (hp n).symm

theorem sub_mem {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    p-ML p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
  classical
  let I := Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})
  let q : MvPolynomial σ (ZMod 2) →+* MvPolynomial σ (ZMod 2) ⧸ I := Ideal.Quotient.mk I
  have hX (i : σ) : (q (X i))^2=q (X i) := by
    have hi : X i^2-X i∈I := Ideal.subset_span (Or.inr ⟨i,rfl⟩)
    have hz : q (X i^2-X i)=0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
    simpa only [map_sub,map_pow,sub_eq_zero] using hz
  have hmono (s : σ →₀ ℕ) (a : ZMod 2) : q (ML (monomial s a))=q (monomial s a) := by
    rw [ml_monomial,monomial_eq,monomial_eq,map_mul,map_mul]
    congr 1
    simp only [Finsupp.prod,sqfree_support,map_prod,map_pow]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [sqfree,Finsupp.mapRange_apply] using power_min (q (X i)) (hX i) (s i)
  have he : q (ML p)=q p := by
    conv_lhs => rw [p.as_sum,map_sum,map_sum]
    conv_rhs => rw [p.as_sum,map_sum]
    exact Finset.sum_congr rfl (fun s hs => hmono s (coeff s p))
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change q (p-ML p)=0
  rw [map_sub,he,sub_self]

theorem closed {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2))
    (hp : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) :
    ML p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
  have hh := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).sub_mem hp (sub_mem G p)
  convert hh using 1 <;> ring

end AC02Frege.P2MBooleanIdealMultilinearization
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
-- Inlined Solutions.P2MBooleanLeadingMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.P2MBooleanLeadingMonomials

open MvPolynomial P2MBooleanAlgebra P2MBooleanBasis
open scoped MonomialOrder

variable {V : Type}

lemma ml_expansion (p : MvPolynomial V (ZMod 2)) :
    ML p = ∑ d ∈ p.support, monomial (sqfree d) (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum,ml_monomial]

lemma sqfree_le (d : V →₀ ℕ) : sqfree d ≤ d := by
  intro i
  exact min_le_left _ _

lemma degree_ml_le (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) :
    m.toSyn (m.degree (ML p)) ≤ m.toSyn (m.degree p) := by
  classical
  apply m.degree_le_iff.mpr
  intro d hd
  rw [ml_expansion] at hd
  obtain ⟨s,hs,hds⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have he : d = sqfree s := Finset.mem_singleton.mp (support_monomial_subset hds)
  rw [he]
  exact (m.toSyn_monotone (sqfree_le s)).trans (m.le_degree hs)

lemma coeff_leading_ml (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : coeff (m.degree p) (ML p) = m.leadingCoeff p := by
  classical
  rw [ml_expansion,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (m.degree p)]
  · rw [sqfree_eq_self _ hfree,MvPolynomial.coeff_monomial,if_pos rfl]
    rfl
  · intro d hd hne
    have hs : sqfree d ≠ m.degree p := by
      intro he
      have hle : m.toSyn (m.degree p) ≤ m.toSyn d := by
        rw [← he]
        exact m.toSyn_monotone (sqfree_le d)
      have hd' : d = m.degree p := m.toSyn.injective (le_antisymm (m.le_degree hd) hle)
      exact hne hd'
    simp only [MvPolynomial.coeff_monomial,if_neg hs]
  · intro hnot
    exact False.elim (hnot (m.degree_mem_support hp))

lemma leading_ml {m : MonomialOrder V} {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : ML p ≠ 0 ∧ m.degree (ML p) = m.degree p := by
  have hc : coeff (m.degree p) (ML p) ≠ 0 := by
    rw [coeff_leading_ml m p hp hfree]
    exact m.leadingCoeff_ne_zero_iff.mpr hp
  have hn : ML p ≠ 0 := by intro hz; simp [hz] at hc
  refine ⟨hn,m.toSyn.injective (le_antisymm (degree_ml_le m p) (m.le_degree (mem_support_iff.mpr hc)))⟩

lemma indicator_insert [DecidableEq V] {S : Finset V} {v : V} (hv : v ∉ S) :
    Finsupp.indicator S (fun _ _ => (1 : ℕ))+Finsupp.single v 1 =
      Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i = v
  · subst i; simp [Finsupp.indicator_apply,hv]
  · by_cases hS : i ∈ S <;> simp [Finsupp.indicator_apply,hi,hS]

/-- Multiplication by a variable absent from the leading monomial preserves that extension
as the leading monomial after Boolean multilinearization. -/
theorem leading_extension [DecidableEq V] (m : MonomialOrder V) {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (S : Finset V) (hS : m.degree p = Finsupp.indicator S (fun _ _ => 1))
    (v : V) (hv : v ∉ S) :
    ML (p*X v) ≠ 0 ∧ m.degree (ML (p*X v)) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  have hX : (X v : MvPolynomial V (ZMod 2)) ≠ 0 := X_ne_zero v
  have hprod : p*X v ≠ 0 := mul_ne_zero hp hX
  have hd : m.degree (p*X v) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
    rw [m.degree_mul hp hX,m.degree_X,hS,indicator_insert hv]
  have hfree : ∀ i, m.degree (p*X v) i ≤ 1 := by
    intro i
    rw [hd]
    simp only [Finsupp.indicator_apply]
    split_ifs <;> omega
  obtain ⟨hn,he⟩ := leading_ml hprod hfree
  exact ⟨hn,he.trans hd⟩

end AC02Frege.P2MBooleanLeadingMonomials
end

section
-- Inlined Solutions.P2MBooleanIrreducibleDownset

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanIrreducibleDownset

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanLeadingMonomials

variable {σ : Type} [DecidableEq σ]

lemma of_insert (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (S : Finset σ) (v : σ) (hv : v∉S) (h : IsIrred m G (insert v S)) : IsIrred m G S := by
  intro q hq hn he
  have hd : m.degree q=Finsupp.indicator S (fun _ _ => 1) := by
    simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using he
  obtain ⟨hp,hdeg⟩ := leading_extension m hn S hd v hv
  have hI := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_right (X v) hq.2
  have hML := AC02Frege.P2MBooleanIdealMultilinearization.closed G (q*X v) hI
  apply h (ML (q*X v)) ⟨ml_multilinear _,hML⟩ hp
  simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using hdeg

theorem subset (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (S T : Finset σ) (hST : S⊆T) (hT : IsIrred m G T) : IsIrred m G S := by
  have hh : ∀ U : Finset σ, Disjoint S U → IsIrred m G (S∪U) → IsIrred m G S := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro hdis h; simpa using h
    | @insert v U hvU ih =>
      intro hdis h
      have hvS : v∉S := by
        intro hv
        exact (Finset.disjoint_left.mp hdis) hv (Finset.mem_insert_self _ _)
      have hv : v∉S∪U := by simpa only [Finset.mem_union,not_or] using And.intro hvS hvU
      have h' : IsIrred m G (S∪U) := by
        apply of_insert m G (S∪U) v hv
        simpa only [Finset.union_insert] using h
      exact ih (Finset.disjoint_of_subset_right (Finset.subset_insert v U) hdis) h'
  apply hh (T\S) (Finset.disjoint_left.mpr (by intro x hx hx'; exact (Finset.mem_sdiff.mp hx').2 hx))
  rwa [Finset.union_sdiff_of_subset hST]

end SemAC02.Supplement.P2MBooleanIrreducibleDownset
end

section
-- Inlined Solutions.P2MExpansionNormalFormFixed

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionNormalFormFixed

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

noncomputable def normalSpan {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2) (xMon '' {t | IsIrred m G t})

theorem normal_multilinear {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G) : IsMultilinear p := by
  apply (mem_restrictDegree σ p 1).mp
  apply (show normalSpan m G ≤ restrictDegree σ (ZMod 2) 1 from ?_) hp
  apply Submodule.span_le.mpr
  rintro q ⟨t,ht,rfl⟩
  exact (mem_restrictDegree σ _ 1).mpr (xMon_multilinear t)

theorem supported {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2))) :
    normalSpan m G ≤ restrictSupport (ZMod 2)
      {d | ∀ q∈idealB G, q≠0 → m.degree q≠d} := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  rw [xMon_eq_monomial]
  apply (monomial_mem_restrictSupport (ZMod 2)).mpr
  left
  intro q hq hn
  have hh := ht q hq hn
  simpa only [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero] using hh

theorem zero_of_ideal {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G)
    (hI : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : p=0 := by
  by_contra hn
  have hstd := supported m G hp
  exact (hstd (m.degree_mem_support hn)) p ⟨normal_multilinear m G p hp,hI⟩ hn rfl

theorem nf_fixed {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (t : Finset σ) (ht : IsIrred m G t) : nf m G (xMon t)=xMon t := by
  have hp : xMon t∈normalSpan m G := Submodule.subset_span ⟨t,ht,rfl⟩
  have hex : ∃ q∈normalSpan m G,
      xMon t-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := ⟨xMon t,hp,by simp⟩
  have hchoice : nf m G (xMon t)∈normalSpan m G ∧
      xMon t-nf m G (xMon t)∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
    unfold normalSpan at hex
    simp only [nf,dif_pos hex,normalSpan]
    exact hex.choose_spec
  exact (sub_eq_zero.mp (zero_of_ideal m G _ ((normalSpan m G).sub_mem hp hchoice.1) hchoice.2)).symm

theorem expOp_fixed {σ L R : Type} [DecidableEq σ] [Fintype L] [DecidableEq L] [Fintype R]
    [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ)
    (ht : IsIrred m P.F0 t) (hSup : supS P.graph s (t.image P.cluster)=∅) : expOp P m s t=xMon t := by
  unfold expOp
  rw [hSup]
  have he : P.F0 ∪ {p | ∃ u∈(∅ : Finset L), p∈P.Fu u}=P.F0 := by ext p; simp
  rw [he]
  exact nf_fixed m P.F0 t ht

end SemAC02.Supplement.P2MExpansionNormalFormFixed
end

section
-- Inlined Solutions.P2MLinearStandardMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.P2MLinearStandardMonomials

open MvPolynomial
open scoped MonomialOrder

variable {σ : Type}

def Standard (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (d : σ →₀ ℕ) : Prop := ∀ p ∈ S, p ≠ 0 → m.degree p ≠ d

lemma leadingCoeff_one (m : MonomialOrder σ) {p : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0) :
    m.leadingCoeff p = 1 := by
  have hn := m.leadingCoeff_ne_zero_iff.mpr hp
  generalize m.leadingCoeff p = a at *
  fin_cases a <;> simp_all

lemma cancel_lt (m : MonomialOrder σ) {p q : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0)
    (hq : q ≠ 0) (hd : m.degree q = m.degree p) :
    m.toWithBotSyn (m.withBotDegree (p-q)) < m.toWithBotSyn (m.withBotDegree p) := by
  classical
  rw [m.withBotDegree_lt_withBotDegree_iff]
  by_cases hz : p-q = 0
  · exact Or.inr ⟨hz,hp⟩
  · apply Or.inl
    have hle : m.toSyn (m.degree (p-q)) ≤ m.toSyn (m.degree p) := by
      exact m.degree_sub_le.trans (by rw [hd,max_self])
    apply lt_of_le_of_ne hle
    intro he
    have he' : m.degree (p-q) = m.degree p := m.toSyn.injective he
    have hc : coeff (m.degree p) (p-q) ≠ 0 := by
      rw [← he']
      exact m.coeff_degree_ne_zero_iff.mpr hz
    apply hc
    rw [coeff_sub]
    have hp1 : coeff (m.degree p) p = 1 := leadingCoeff_one m hp
    have hq1 : coeff (m.degree p) q = 1 := by rw [← hd]; exact leadingCoeff_one m hq
    rw [hp1,hq1,sub_self]

/-- Linear elimination modulo an arbitrary subspace, preserving the leading-degree bound.
Unlike polynomial ideal division, this only subtracts scalar multiples of subspace vectors. -/
theorem remainder (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧
      m.toWithBotSyn (m.withBotDegree r) ≤ m.toWithBotSyn (m.withBotDegree p) ∧
      ∀ d ∈ r.support, Standard m S d := by
  classical
  have hwf : WellFounded (fun p q : MvPolynomial σ (ZMod 2) =>
      m.toWithBotSyn (m.withBotDegree p) < m.toWithBotSyn (m.withBotDegree q)) :=
    InvImage.wf _ wellFounded_lt
  induction p using hwf.induction with
  | h p ih =>
    by_cases hp : p = 0
    · subst p
      exact ⟨0,by simp,le_rfl,by simp⟩
    by_cases hstd : Standard m S (m.degree p)
    · let t := m.leadingTerm p
      have ht : t ≠ 0 := (m.leadingTerm_eq_zero_iff p).not.mpr hp
      have htd : m.degree t = m.degree p := m.degree_leadingTerm p
      have hlt := cancel_lt m hp ht htd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-t) hlt
      refine ⟨t+r,?_,?_,?_⟩
      · convert hrS using 1 <;> ring
      · exact (m.withBotDegree_add_le t r).trans (max_le
          (by rw [m.withBotDegree_leadingTerm]) (hrle.trans hlt.le))
      · intro d hd
        have hmem := (Finset.mem_union.mp (MvPolynomial.support_add hd))
        rcases hmem with hdt | hdr
        · have he : d = m.degree p := by simpa only [t,m.support_leadingTerm' hp,Finset.mem_singleton] using hdt
          simpa only [he] using hstd
        · exact hrstd d hdr
    · simp only [Standard,not_forall,_root_.not_imp,not_not] at hstd
      obtain ⟨q,hqS,hq,hqd⟩ := hstd
      have hlt := cancel_lt m hp hq hqd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-q) hlt
      refine ⟨r,?_,hrle.trans hlt.le,hrstd⟩
      convert S.add_mem hqS hrS using 1 <;> ring

noncomputable def supported (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {d | Standard m S d}

theorem supported_disjoint (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) : Disjoint (supported m S) S := by
  rw [Submodule.disjoint_def]
  intro p hp hpS
  by_contra hn
  exact (hp (m.degree_mem_support hn)) p hpS hn rfl

/-- The graded version used to count leading monomials in a bounded-degree solution space. -/
theorem remainder_totalDegree [LinearOrder σ] [WellFoundedGT σ]
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧ r.totalDegree ≤ p.totalDegree ∧
      ∀ d ∈ r.support, Standard MonomialOrder.degLex S d := by
  classical
  obtain ⟨r,hrS,hrle,hrstd⟩ := remainder MonomialOrder.degLex S p
  refine ⟨r,hrS,?_,hrstd⟩
  exact MvPolynomial.degLex_totalDegree_monotone
    ((MonomialOrder.withBotDegree_le_withBotDegree_iff _ _).mp hrle).1

end AC02Frege.P2MLinearStandardMonomials
end

section
-- Inlined Solutions.P2MDegreeCompatibleOrder

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDegreeCompatibleOrder

open MvPolynomial

lemma exponent_sum_mono {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (a b : σ →₀ ℕ) (hab : m.toSyn a ≤ m.toSyn b) : Finsupp.degree a ≤ Finsupp.degree b := by
  by_contra hn
  exact (not_lt_of_ge hab) (hm b a (lt_of_not_ge hn))

theorem totalDegree_eq {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (p : MvPolynomial σ (ZMod 2)) : p.totalDegree=Finsupp.degree (m.degree p) := by
  by_cases hz : p=0
  · subst p
    simp
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact exponent_sum_mono m hm d (m.degree p) (m.le_degree hd)
  · exact le_totalDegree (m.degree_mem_support hz)

theorem totalDegree_mono {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (p q : MvPolynomial σ (ZMod 2)) (hle : m.toSyn (m.degree p) ≤ m.toSyn (m.degree q)) :
    p.totalDegree ≤ q.totalDegree := by
  rw [totalDegree_eq m hm p,totalDegree_eq m hm q]
  exact exponent_sum_mono m hm _ _ hle

end SemAC02.Supplement.P2MDegreeCompatibleOrder
end

section
-- Inlined Solutions.P2MBooleanIdealNormalForm

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanIdealNormalForm

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MExpansionNormalFormFixed

noncomputable def idealSpace {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictDegree σ (ZMod 2) 1 ⊓
    (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).restrictScalars (ZMod 2)

lemma mem_space {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    p∈idealSpace G ↔ p∈idealB G := by
  change p∈restrictDegree σ (ZMod 2) 1 ∧ p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ↔ _
  rw [mem_restrictDegree]
  rfl

theorem exists_remainder {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    ∃ r∈normalSpan m G, p-r∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ∧ r.totalDegree ≤ p.totalDegree := by
  classical
  obtain ⟨r,hrI,hrle,hrstd⟩ := AC02Frege.P2MLinearStandardMonomials.remainder m (idealSpace G) p
  have hrM : IsMultilinear (p-r) := ((mem_space G _).mp hrI).1
  have hrml : IsMultilinear r := by
    apply (mem_restrictDegree σ r 1).mp
    have hpm := (mem_restrictDegree σ p 1).mpr hp
    have hrm := (mem_restrictDegree σ (p-r) 1).mpr hrM
    convert (restrictDegree σ (ZMod 2) 1).sub_mem hpm hrm using 1 <;> ring
  refine ⟨r,?_,((mem_space G _).mp hrI).2,?_⟩
  · rw [r.as_sum]
    apply Submodule.sum_mem
    intro d hd
    have hfree := hrml d hd
    rw [squarefree_monomial d _ hfree]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨d.support,?_,rfl⟩
    intro q hq hn he
    apply hrstd d hd q ((mem_space G q).mpr hq) hn
    have hlead : m.degree (xMon d.support)=d := by
      rw [xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero,←squarefree_eq_indicator d hfree]
    exact he.trans hlead
  · apply P2MDegreeCompatibleOrder.totalDegree_mono m hm r p
    exact ((MonomialOrder.withBotDegree_le_withBotDegree_iff _ _).mp hrle).1

theorem unique {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p r q : MvPolynomial σ (ZMod 2)) (hr : r∈normalSpan m G) (hq : q∈normalSpan m G)
    (hpr : p-r∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}))
    (hpq : p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : r=q := by
  apply sub_eq_zero.mp
  apply zero_of_ideal m G _ ((normalSpan m G).sub_mem hr hq)
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).sub_mem hpq hpr using 1 <;> ring

theorem spec {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G p∈normalSpan m G ∧ p-nf m G p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ∧
      (nf m G p).totalDegree ≤ p.totalDegree := by
  obtain ⟨r,hr,hpr,hrdeg⟩ := exists_remainder m hm G p hp
  have hex : ∃ q∈normalSpan m G, p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := ⟨r,hr,hpr⟩
  have hchoice : nf m G p∈normalSpan m G ∧
      p-nf m G p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by
    unfold normalSpan at hex
    simp only [nf,dif_pos hex,normalSpan]
    exact hex.choose_spec
  refine ⟨hchoice.1,hchoice.2,?_⟩
  rw [unique m G p (nf m G p) r hchoice.1 hr hchoice.2 hpr]
  exact hrdeg

end SemAC02.Supplement.P2MBooleanIdealNormalForm
end

section
-- Inlined Solutions.P2MBooleanNormalFormRestrictions

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormRestrictions

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed

variable {σ : Type} [DecidableEq σ]

noncomputable def restrict (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2) :
    MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  aeval (fun v => if keep v then X v else C (α v))

theorem monomial (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2) (t : Finset σ) :
    restrict keep α (xMon t)=(∏ v∈t.filter (fun v => ¬ keep v), α v) • xMon (t.filter keep) := by
  rw [restrict,xMon,map_prod]
  simp only [aeval_X]
  rw [smul_eq_C_mul,map_prod,xMon,Finset.prod_filter,Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases h : keep v <;> simp [h]


theorem multilinear (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) : IsMultilinear (restrict keep α p) := by
  apply (mem_restrictDegree σ _ 1).mp
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [AC02Frege.P2MBooleanBasis.squarefree_monomial d _ (hp d hd),map_smul,monomial]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact (mem_restrictDegree σ _ 1).mpr (xMon_multilinear _)

theorem normal_span (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G) : restrict keep α p∈normalSpan m G := by
  change p∈Submodule.span (ZMod 2) (xMon '' {t | IsIrred m G t}) at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    rw [monomial]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨t.filter keep,
      P2MBooleanIrreducibleDownset.subset m G (t.filter keep) t (Finset.filter_subset _ _) ht,rfl⟩
  | zero => rw [map_zero]; exact (normalSpan m G).zero_mem
  | add p q hp hq ihp ihq => rw [map_add]; exact (normalSpan m G).add_mem ihp ihq
  | smul a p hp ih => rw [map_smul]; exact (normalSpan m G).smul_mem a ih

end SemAC02.Supplement.P2MBooleanNormalFormRestrictions
end

section
-- Inlined Solutions.P2MClusterRestrictionBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MClusterRestrictionBasics

open MvPolynomial AC02Frege P2MExpansionNormalFormFixed

variable {σ L R : Type} [DecidableEq σ] [DecidableEq R]

theorem as_restriction (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) :
    P.substCluster v α p=P2MBooleanNormalFormRestrictions.restrict (fun x => P.cluster x≠v) α p := by
  unfold ClusteredRep.substCluster P2MBooleanNormalFormRestrictions.restrict
  apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
  funext x
  by_cases h : P.cluster x=v <;> simp [h]

theorem normal_span (P : ClusteredRep σ L R) (m : MonomialOrder σ)
    (G : Set (MvPolynomial σ (ZMod 2))) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈normalSpan m G) : P.substCluster v α p∈normalSpan m G := by
  rw [as_restriction]
  exact P2MBooleanNormalFormRestrictions.normal_span m G _ α p hp


theorem multilinear (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) : IsMultilinear (P.substCluster v α p) := by
  rw [as_restriction]
  exact P2MBooleanNormalFormRestrictions.multilinear _ α p hp

theorem untouched (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (hvars : ∀ x∈p.vars, P.cluster x≠v) : P.substCluster v α p=p := by
  let φ : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
    aeval (fun x => if P.cluster x=v then C (α x) else X x)
  have hφ : φ p=p := by
    change φ.toRingHom p=RingHom.id (MvPolynomial σ (ZMod 2)) p
    apply MvPolynomial.hom_congr_vars
    · ext a
      simp [φ]
    · intro x hx hx'
      simp [φ,hvars x hx]
    · rfl
  have he : P.substCluster v α p=φ p := by
    unfold ClusteredRep.substCluster
    dsimp only [φ]
    apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
    funext x
    by_cases h : P.cluster x=v <;> simp [h]
  exact he.trans hφ


theorem sub (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p q : MvPolynomial σ (ZMod 2)) :
    P.substCluster v α (p-q)=P.substCluster v α p-P.substCluster v α q := by
  simp only [as_restriction,map_sub]

theorem monomial_untouched (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (t : Finset σ) (hvars : ∀ x∈t, P.cluster x≠v) : P.substCluster v α (xMon t)=xMon t := by
  unfold ClusteredRep.substCluster
  rw [xMon,map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [aeval_X,if_neg (hvars x hx)]


theorem vars_avoid (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) (x : σ) (hx : x∈(P.substCluster v α p).vars) : P.cluster x≠v := by
  rw [as_restriction] at hx
  unfold P2MBooleanNormalFormRestrictions.restrict at hx
  rw [MvPolynomial.aeval_eq_bind₁] at hx
  obtain ⟨i,hi,hxi⟩ := MvPolynomial.mem_vars_bind₁ _ _ hx
  by_cases h : P.cluster i≠v
  · simp only [if_pos h,vars_X,Finset.mem_singleton] at hxi
    subst x
    exact h
  · simp only [if_neg h,vars_C,Finset.notMem_empty] at hxi

theorem untouched_axiom [Fintype L] [DecidableEq L]
    (P : ClusteredRep σ L R) (u : L) (v : R) (α : σ → ZMod 2)
    (hnot : ¬ P.graph.Adj u v) (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.Fu u) :
    P.substCluster v α p=p := by
  apply untouched P v α p
  intro x hx he
  exact hnot ⟨p,hp,x,hx,he⟩

theorem background_assignment [Fintype L] [DecidableEq L]
    (P : ClusteredRep σ L R) (hP : P.IsRespectful) (v : R) (u : L) (huv : P.graph.Adj u v) :
    ∃ α : σ → ZMod 2, ∀ g∈P.F0,
      (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g)=0) ∨
      (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g)=eval (toF2 y) g) := by
  obtain ⟨α,hFu,hF0⟩ := hP {u} v u (by simp [huv])
  exact ⟨α,hF0⟩

end SemAC02.Supplement.P2MClusterRestrictionBasics
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
-- Inlined Solutions.P2MRespectfulPolynomialAssignment

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRespectfulPolynomialAssignment

open MvPolynomial AC02Frege P2MBooleanFunctionPolynomials

theorem assignment {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [DecidableEq R] (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (J : Finset L) (v : R) (u : L)
    (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u}) :
    ∃ α : σ → ZMod 2, (∀ p∈P.Fu u, P.substCluster v α p=0) ∧
      ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g := by
  obtain ⟨α,hFu,hF0⟩ := hP J v u hboundary
  refine ⟨α,?_,?_⟩
  · intro p hp
    have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
    apply multilinear_ext_bool (P2MClusterRestrictionBasics.multilinear P v α p hpml)
      (by intro s hs; simp at hs)
    intro y
    simpa only [map_zero] using hFu p hp y
  · intro g hg
    have hgml : IsMultilinear g := hml g (Or.inl hg)
    rcases hF0 g hg with hzero | heq
    · left
      apply multilinear_ext_bool (P2MClusterRestrictionBasics.multilinear P v α g hgml)
        (by intro s hs; simp at hs)
      intro y
      simpa only [map_zero] using hzero y
    · right
      exact multilinear_ext_bool (P2MClusterRestrictionBasics.multilinear P v α g hgml) hgml heq

end SemAC02.Supplement.P2MRespectfulPolynomialAssignment
end

section
-- Inlined Solutions.P2MClusterLocalIdeals

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MClusterLocalIdeals

open MvPolynomial AC02Frege

variable {σ L R : Type} [DecidableEq σ] [DecidableEq L] [DecidableEq R]

noncomputable def axioms (P : ClusteredRep σ L R) (J : Finset L) : Set (MvPolynomial σ (ZMod 2)) :=
  P.F0 ∪ {p | ∃ u∈J, p∈P.Fu u}

noncomputable def ideal (P : ClusteredRep σ L R) (J : Finset L) : Ideal (MvPolynomial σ (ZMod 2)) :=
  Ideal.span (axioms P J ∪ {p | ∃ i : σ, p=X i^2-X i})

theorem axioms_mono (P : ClusteredRep σ L R) (J K : Finset L) (hJK : J⊆K) : axioms P J⊆axioms P K := by
  rintro p (hp | ⟨u,hu,hp⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨u,hJK hu,hp⟩

theorem ideal_mono (P : ClusteredRep σ L R) (J K : Finset L) (hJK : J⊆K) : ideal P J ≤ ideal P K :=
  Ideal.span_mono (Set.union_subset_union_left _ (axioms_mono P J K hJK))

theorem restriction_maps [Fintype L] (P : ClusteredRep σ L R) (J : Finset L) (u : L) (v : R)
    (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u}) (α : σ → ZMod 2)
    (hFu : ∀ p∈P.Fu u, P.substCluster v α p=0)
    (hF0 : ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g)
    (q : MvPolynomial σ (ZMod 2)) (hq : q∈ideal P J) : P.substCluster v α q∈ideal P (J.erase u) := by
  let φ := P2MBooleanNormalFormRestrictions.restrict (fun x => P.cluster x≠v) α
  rw [P2MClusterRestrictionBasics.as_restriction]
  change φ q∈ideal P (J.erase u)
  have hle : ideal P J ≤ Ideal.comap φ.toRingHom (ideal P (J.erase u)) := by
    apply Ideal.span_le.mpr
    intro p hp
    change φ p∈ideal P (J.erase u)
    rcases hp with (hbg | ⟨u',hu',hp⟩) | ⟨x,rfl⟩
    · change φ p∈ideal P (J.erase u)
      rw [←P2MClusterRestrictionBasics.as_restriction]
      rcases hF0 p hbg with he | he
      · rw [he]; exact (ideal P (J.erase u)).zero_mem
      · rw [he]; exact Ideal.subset_span (Or.inl (Or.inl hbg))
    · by_cases he : u'=u
      · subst u'
        change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
        rw [←P2MClusterRestrictionBasics.as_restriction,hFu p hp]
        exact (ideal P (J.erase u)).zero_mem
      · have hnot : ¬ P.graph.Adj u' v := by
          intro hAdj
          have hm : u'∈J.filter (fun a => P.graph.Adj a v) := Finset.mem_filter.mpr ⟨hu',hAdj⟩
          rw [hboundary] at hm
          exact he (Finset.mem_singleton.mp hm)
        change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
        rw [←P2MClusterRestrictionBasics.as_restriction,P2MClusterRestrictionBasics.untouched_axiom P u' v α hnot p hp]
        exact Ideal.subset_span (Or.inl (Or.inr ⟨u',Finset.mem_erase.mpr ⟨he,hu'⟩,hp⟩))
    · have hx : φ (X x)=if P.cluster x≠v then X x else C (α x) := by
        simp only [φ,P2MBooleanNormalFormRestrictions.restrict,aeval_X]
      rw [map_sub,map_pow,hx]
      by_cases h : P.cluster x=v
      · rw [if_neg (not_not.mpr h)]
        have hval : (α x)^2=α x := by
          rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (α x) with he | he <;> simp [he]
        rw [←map_pow,hval,sub_self]
        exact (ideal P (J.erase u)).zero_mem
      · rw [if_pos h]
        exact Ideal.subset_span (Or.inr ⟨x,rfl⟩)
  exact hle hq

end SemAC02.Supplement.P2MClusterLocalIdeals
end

section
-- Inlined Solutions.P2MBooleanNormalSpanMonotonicity

namespace SemAC02.Supplement.P2MBooleanNormalSpanMonotonicity

open MvPolynomial AC02Frege P2MExpansionNormalFormFixed

theorem irreducible {σ : Type} (m : MonomialOrder σ) (G H : Set (MvPolynomial σ (ZMod 2)))
    (hGH : G⊆H) (t : Finset σ) (ht : IsIrred m H t) : IsIrred m G t := by
  intro q hq hn he
  apply ht q ⟨hq.1,?_⟩ hn he
  exact (Ideal.span_mono (Set.union_subset_union_left _ hGH)) hq.2

theorem span {σ : Type} (m : MonomialOrder σ) (G H : Set (MvPolynomial σ (ZMod 2)))
    (hGH : G⊆H) : normalSpan m H ≤ normalSpan m G := by
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  exact Submodule.subset_span ⟨t,irreducible m G H hGH t ht,rfl⟩

end SemAC02.Supplement.P2MBooleanNormalSpanMonotonicity
end

section
-- Inlined Solutions.P2MClusterNormalFormPeeling

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MClusterNormalFormPeeling

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed P2MBooleanIdealNormalForm P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L] [DecidableEq R]

theorem peel (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (u : L) (v : R) (hboundary : J.filter (fun u' => P.graph.Adj u' v)={u})
    (t : Finset σ) (hvars : ∀ x∈t, P.cluster x≠v) :
    nf m (axioms P J) (xMon t)=nf m (axioms P (J.erase u)) (xMon t) := by
  obtain ⟨α,hFu,hF0⟩ := P2MRespectfulPolynomialAssignment.assignment P hP hml J v u hboundary
  let r := nf m (axioms P J) (xMon t)
  have hr := spec m hm (axioms P J) (xMon t) (xMon_multilinear t)
  have hφr : P.substCluster v α r∈normalSpan m (axioms P J) :=
    P2MClusterRestrictionBasics.normal_span P m (axioms P J) v α r hr.1
  have hφrSmall : P.substCluster v α r∈normalSpan m (axioms P (J.erase u)) :=
    P2MBooleanNormalSpanMonotonicity.span m _ _ (axioms_mono P (J.erase u) J (Finset.erase_subset _ _)) hφr
  have hmap := restriction_maps P J u v hboundary α hFu hF0 (xMon t-r) hr.2.1
  rw [P2MClusterRestrictionBasics.sub,P2MClusterRestrictionBasics.monomial_untouched P v α t hvars] at hmap
  have heBig : r=P.substCluster v α r := unique m (axioms P J) (xMon t) r _ hr.1 hφr hr.2.1
    ((ideal_mono P (J.erase u) J (Finset.erase_subset _ _)) hmap)
  have hrSmall := spec m hm (axioms P (J.erase u)) (xMon t) (xMon_multilinear t)
  have heSmall : nf m (axioms P (J.erase u)) (xMon t)=P.substCluster v α r :=
    unique m _ (xMon t) _ _ hrSmall.1 hφrSmall hrSmall.2.1 hmap
  exact heBig.trans heSmall.symm

end SemAC02.Supplement.P2MClusterNormalFormPeeling
end

section
-- Inlined Solutions.P2MBoundaryUnion

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBoundaryUnion

open PCNonBool

variable {L R : Type} [DecidableEq L] [Fintype R] [DecidableEq R]

lemma filter_singleton_of_subset (G : BipGraph L R) (J K : Finset L) (v : R) (u : L)
    (hJK : J⊆K) (hK : K.filter (fun u' => G.Adj u' v)={u}) (hu : u∈J) :
    J.filter (fun u' => G.Adj u' v)={u} := by
  have huK : u∈K.filter (fun u' => G.Adj u' v) := by rw [hK]; simp
  have huv := (Finset.mem_filter.mp huK).2
  apply Finset.Subset.antisymm
  · intro w hw
    have hwK : w∈K.filter (fun u' => G.Adj u' v) := Finset.mem_filter.mpr ⟨hJK (Finset.mem_filter.mp hw).1,(Finset.mem_filter.mp hw).2⟩
    rwa [hK] at hwK
  · intro w hw
    have he : w=u := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_filter.mpr ⟨hu,huv⟩

theorem subset (G : BipGraph L R) (J K : Finset L) :
    boundaryOn G Finset.univ (J∪K)⊆boundaryOn G Finset.univ J∪boundaryOn G Finset.univ K := by
  intro v hv
  obtain ⟨u,he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈(J∪K).filter (fun u' => G.Adj u' v) := by rw [he]; simp
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with huJ | huK
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [filter_singleton_of_subset G J (J∪K) v u Finset.subset_union_left he huJ,Finset.card_singleton]
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [filter_singleton_of_subset G K (J∪K) v u Finset.subset_union_right he huK,Finset.card_singleton]

end P2MProofComplexity.P2MBoundaryUnion
end

section
-- Inlined Solutions.P2MUnionClosedFiniteFamily

namespace P2MProofComplexity.P2MUnionClosedFiniteFamily

variable {V : Type} [DecidableEq V]

theorem union_all_mem (E : Finset (Finset V)) (hzero : ∅∈E)
    (hunion : ∀ A∈E, ∀ B∈E, A∪B∈E) : E.biUnion id∈E := by
  have hh : ∀ T : Finset (Finset V), T⊆E → T.biUnion id∈E := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro h; simpa using hzero
    | @insert A T hAT ih =>
      intro h
      rw [Finset.biUnion_insert]
      exact hunion A (h (Finset.mem_insert_self _ _)) _ (ih (Finset.Subset.trans (Finset.subset_insert A T) h))
  exact hh E Finset.Subset.rfl

end P2MProofComplexity.P2MUnionClosedFiniteFamily
end

section
-- Inlined Solutions.P2MExpansionSmallSupports

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSmallSupports

open PCNonBool Classical

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem properties (G : BipGraph L R) (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp G s c)
    (A : Finset R) (hA : (A.card : ℝ) ≤ c*s/2) :
    boundaryOn G Finset.univ (supS G s A)⊆A ∧
      ((supS G s A).card : ℝ) ≤ (A.card : ℝ)/c ∧ (A.card : ℝ)/c ≤ s/2 := by
  let E := (Finset.univ : Finset (Finset L)).filter (fun J : Finset L =>
    (J.card : ℝ) ≤ s ∧ boundaryOn G Finset.univ J⊆A)
  have hs : 0 ≤ s := by have hh := Nat.cast_nonneg (α:=ℝ) A.card; nlinarith
  have hzero : ∅∈E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · simpa only [Finset.card_empty,Nat.cast_zero] using hs
    · simp [boundaryOn]
  have hbound : ∀ J∈E, (J.card : ℝ) ≤ (A.card : ℝ)/c := by
    intro J hJ
    have hh := (Finset.mem_filter.mp hJ).2
    have hb := hexp J hh.1
    have hcard : ((boundaryOn G Finset.univ J).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card hh.2
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  have hhalf : (A.card : ℝ)/c ≤ s/2 := (div_le_iff₀ hc).mpr (by nlinarith)
  have hunion : ∀ J∈E, ∀ K∈E, J∪K∈E := by
    intro J hJ K hK
    have hj := (hbound J hJ).trans hhalf
    have hk := (hbound K hK).trans hhalf
    have hcard : ((J∪K).card : ℝ) ≤ (J.card : ℝ)+(K.card : ℝ) := by
      exact_mod_cast Finset.card_union_le J K
    have hbdry : boundaryOn G Finset.univ (J∪K)⊆A :=
      (P2MProofComplexity.P2MBoundaryUnion.subset G J K).trans (Finset.union_subset
        (Finset.mem_filter.mp hJ).2.2 (Finset.mem_filter.mp hK).2.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith,hbdry⟩
  have hmem := P2MProofComplexity.P2MUnionClosedFiniteFamily.union_all_mem E hzero hunion
  have he : E.biUnion id=supS G s A := by
    ext u
    simp only [E,supS,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,id_eq]
  have hprop := (Finset.mem_filter.mp hmem).2
  rw [he] at hprop
  refine ⟨hprop.2,?_,hhalf⟩
  have hh := hbound _ hmem
  rwa [he] at hh

end SemAC02.Supplement.P2MExpansionSmallSupports
end

section
-- Inlined Solutions.P2MExpansionSupportWitness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSupportWitness

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem contains (G : BipGraph L R) (s : ℝ) (A : Finset R) (J : Finset L)
    (hsize : (J.card : ℝ) ≤ s) (hboundary : boundaryOn G Finset.univ J⊆A) : J⊆supS G s A := by
  classical
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsize,hboundary⟩,hu⟩

theorem monotone (G : BipGraph L R) (s : ℝ) (A B : Finset R) (hAB : A⊆B) :
    supS G s A⊆supS G s B := by
  classical
  intro u hu
  obtain ⟨J,hJ,huJ⟩ := Finset.mem_biUnion.mp hu
  have hh := (Finset.mem_filter.mp hJ).2
  exact contains G s B J hh.1 (hh.2.trans hAB) huJ

theorem outside_boundary (G : BipGraph L R) (s : ℝ) (A : Finset R)
    (hSup : boundaryOn G Finset.univ (supS G s A)⊆A)
    (J : Finset L) (hSJ : supS G s A⊆J) (hneq : J≠supS G s A) (hsize : (J.card : ℝ) ≤ s) :
    ∃ (u : L) (v : R), u∈J ∧ u∉supS G s A ∧ v∉A ∧ J.filter (fun u' => G.Adj u' v)={u} := by
  classical
  have hnot : ¬ boundaryOn G Finset.univ J⊆A := by
    intro hb
    exact hneq (Finset.Subset.antisymm (contains G s A J hsize hb) hSJ)
  obtain ⟨v,hv,hvA⟩ := Finset.not_subset.mp hnot
  obtain ⟨u,hfilter⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈J.filter (fun u' => G.Adj u' v) := by rw [hfilter]; simp
  have huJ := (Finset.mem_filter.mp hu).1
  have huSup : u∉supS G s A := by
    intro huSup
    have hsingle := P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G (supS G s A) J v u hSJ hfilter huSup
    have hvSup : v∈boundaryOn G Finset.univ (supS G s A) := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by rw [hsingle,Finset.card_singleton]⟩
    exact hvA (hSup hvSup)
  exact ⟨u,v,huJ,huSup,hvA,hfilter⟩

end SemAC02.Supplement.P2MExpansionSupportWitness
end

section
-- Inlined Solutions.P2MExpansionNormalFormLocality

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionNormalFormLocality

open MvPolynomial AC02Frege P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem locality (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c) (t : Finset σ)
    (hsize : ((t.image P.cluster).card : ℝ) ≤ c*s/2)
    (J : Finset L) (hSJ : supS P.graph s (t.image P.cluster)⊆J) (hJs : (J.card : ℝ) ≤ s) :
    nf m (axioms P J) (xMon t)=expOp P m s t := by
  have hSup := (P2MExpansionSmallSupports.properties P.graph s c hc hexp (t.image P.cluster) hsize).1
  have hh : ∀ j : ℕ, ∀ J : Finset L, J.card=j → supS P.graph s (t.image P.cluster)⊆J →
      (J.card : ℝ) ≤ s → nf m (axioms P J) (xMon t)=expOp P m s t := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro J hj hSJ hJs
      by_cases he : J=supS P.graph s (t.image P.cluster)
      · subst J
        rfl
      obtain ⟨u,v,hu,huSup,hvA,hboundary⟩ :=
        P2MExpansionSupportWitness.outside_boundary P.graph s (t.image P.cluster) hSup J hSJ he hJs
      have hvars : ∀ x∈t, P.cluster x≠v := by
        intro x hx heq
        exact hvA (Finset.mem_image.mpr ⟨x,hx,heq⟩)
      have hpeel := P2MClusterNormalFormPeeling.peel P hP hml m hm J u v hboundary t hvars
      have hcard : (J.erase u).card < j := by
        have hlt : (J.erase u).card < J.card := Finset.card_lt_card (Finset.erase_ssubset hu)
        exact hlt.trans_eq hj
      have hSJerase : supS P.graph s (t.image P.cluster)⊆J.erase u := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨by intro heq; subst a; exact huSup ha,hSJ ha⟩
      have hJsmall : ((J.erase u).card : ℝ) ≤ s := by
        have hle : ((J.erase u).card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_le_card (Finset.erase_subset u J)
        exact hle.trans hJs
      exact hpeel.trans (ih (J.erase u).card hcard (J.erase u) rfl hSJerase hJsmall)
  exact hh J.card J rfl hSJ hJs

end SemAC02.Supplement.P2MExpansionNormalFormLocality
end

section
-- Inlined Solutions.P2MClusterLocalIdealStability

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MClusterLocalIdealStability

open MvPolynomial AC02Frege P2MClusterLocalIdeals

variable {σ L R : Type} [DecidableEq σ] [DecidableEq L] [DecidableEq R]

theorem stable [Fintype L] (P : ClusteredRep σ L R) (J : Finset L) (v : R)
    (hnot : ∀ u∈J, ¬ P.graph.Adj u v) (α : σ → ZMod 2)
    (hF0 : ∀ g∈P.F0, P.substCluster v α g=0 ∨ P.substCluster v α g=g)
    (q : MvPolynomial σ (ZMod 2)) (hq : q∈ideal P J) : P.substCluster v α q∈ideal P J := by
  let φ := P2MBooleanNormalFormRestrictions.restrict (fun x => P.cluster x≠v) α
  rw [P2MClusterRestrictionBasics.as_restriction]
  change φ q∈ideal P J
  have hle : ideal P J ≤ Ideal.comap φ.toRingHom (ideal P J) := by
    apply Ideal.span_le.mpr
    intro p hp
    change φ p∈ideal P J
    rcases hp with (hbg | ⟨u,hu,hp⟩) | ⟨x,rfl⟩
    · rw [←P2MClusterRestrictionBasics.as_restriction]
      rcases hF0 p hbg with he | he
      · rw [he]; exact (ideal P J).zero_mem
      · rw [he]; exact Ideal.subset_span (Or.inl (Or.inl hbg))
    · change P2MBooleanNormalFormRestrictions.restrict _ α p∈_
      rw [←P2MClusterRestrictionBasics.as_restriction,P2MClusterRestrictionBasics.untouched_axiom P u v α (hnot u hu) p hp]
      exact Ideal.subset_span (Or.inl (Or.inr ⟨u,hu,hp⟩))
    · have hx : φ (X x)=if P.cluster x≠v then X x else C (α x) := by
        simp only [φ,P2MBooleanNormalFormRestrictions.restrict,aeval_X]
      rw [map_sub,map_pow,hx]
      by_cases h : P.cluster x=v
      · rw [if_neg (not_not.mpr h)]
        have hval : (α x)^2=α x := by
          rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (α x) with he | he <;> simp [he]
        rw [←map_pow,hval,sub_self]
        exact (ideal P J).zero_mem
      · rw [if_pos h]
        exact Ideal.subset_span (Or.inr ⟨x,rfl⟩)
  exact hle hq

end SemAC02.Supplement.P2MClusterLocalIdealStability
end

section
-- Inlined Solutions.P2MClusterNormalFormVariables

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MClusterNormalFormVariables

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MClusterLocalIdeals P2MBooleanIdealNormalForm

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L] [DecidableEq R]

theorem absent (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (t : Finset σ) (v : R) (u₀ : L) (hactive : P.graph.Adj u₀ v)
    (hnot : ∀ u∈J, ¬ P.graph.Adj u v) (hvars : ∀ x∈t, P.cluster x≠v) :
    ∀ x∈(nf m (axioms P J) (xMon t)).vars, P.cluster x≠v := by
  obtain ⟨α,hFu,hF0⟩ := P2MRespectfulPolynomialAssignment.assignment P hP hml {u₀} v u₀ (by simp [hactive])
  let r := nf m (axioms P J) (xMon t)
  have hr := spec m hm (axioms P J) (xMon t) (xMon_multilinear t)
  have hpr := P2MClusterRestrictionBasics.normal_span P m (axioms P J) v α r hr.1
  have hmap := P2MClusterLocalIdealStability.stable P J v hnot α hF0 (xMon t-r) hr.2.1
  rw [P2MClusterRestrictionBasics.sub,P2MClusterRestrictionBasics.monomial_untouched P v α t hvars] at hmap
  have he : r=P.substCluster v α r := unique m (axioms P J) (xMon t) r _ hr.1 hpr hr.2.1 hmap
  intro x hx
  change x∈r.vars at hx
  rw [he] at hx
  exact P2MClusterRestrictionBasics.vars_avoid P v α r x hx

theorem active_locality (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (J : Finset L) (t : Finset σ) (x : σ) (hx : x∈(nf m (axioms P J) (xMon t)).vars)
    (u₀ : L) (hactive : P.graph.Adj u₀ (P.cluster x)) :
    (∃ u∈J, P.graph.Adj u (P.cluster x)) ∨ P.cluster x∈t.image P.cluster := by
  by_cases hJ : ∃ u∈J, P.graph.Adj u (P.cluster x)
  · exact Or.inl hJ
  · right
    by_contra hinput
    have hnot : ∀ u∈J, ¬ P.graph.Adj u (P.cluster x) := by
      intro u hu hAdj
      exact hJ ⟨u,hu,hAdj⟩
    have hvars : ∀ y∈t, P.cluster y≠P.cluster x := by
      intro y hy he
      exact hinput (Finset.mem_image.mpr ⟨y,hy,he⟩)
    exact absent P hP hml m hm J t (P.cluster x) u₀ hactive hnot hvars x hx rfl

end SemAC02.Supplement.P2MClusterNormalFormVariables
end

section
-- Inlined Solutions.P2MExpansionMonomialNormalForms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionMonomialNormalForms

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
    P2MExpansionNormalFormFixed P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem normal_span (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : expOp P m s t∈P2MExpansionNormalFormFixed.normalSpan m
      (axioms P (supS P.graph s (t.image P.cluster))) :=
  (P2MBooleanIdealNormalForm.spec m hm _ (xMon t) (xMon_multilinear t)).1

theorem multilinear (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : IsMultilinear (expOp P m s t) :=
  normal_multilinear m _ _ (normal_span P m hm s t)

theorem degree (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) : (expOp P m s t).totalDegree ≤ t.card := by
  have hh := (P2MBooleanIdealNormalForm.spec m hm (axioms P (supS P.graph s (t.image P.cluster)))
    (xMon t) (xMon_multilinear t)).2.2
  exact hh.trans_eq (AC02Frege.P2MBooleanAlgebra.xMon_totalDegree t)

theorem support_card (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) (d : σ →₀ ℕ) (hd : d∈(expOp P m s t).support) : d.support.card ≤ t.card := by
  rw [←squarefree_sum d (multilinear P m hm s t d hd)]
  exact (le_totalDegree hd).trans (degree P m hm s t)

theorem active_locality (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (t : Finset σ) (x : σ) (hx : x∈(expOp P m s t).vars)
    (u : L) (hu : P.graph.Adj u (P.cluster x)) :
    (∃ u∈supS P.graph s (t.image P.cluster), P.graph.Adj u (P.cluster x)) ∨
      P.cluster x∈t.image P.cluster :=
  P2MClusterNormalFormVariables.active_locality P hP hml m hm _ t x hx u hu

end SemAC02.Supplement.P2MExpansionMonomialNormalForms
end

section
-- Inlined Solutions.P2MExpansionSupportClosure

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionSupportClosure

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem boundary_control (G : BipGraph L R) (J K : Finset L) (A B : Finset R)
    (hJ : boundaryOn G Finset.univ J⊆B) (hK : boundaryOn G Finset.univ K⊆A)
    (hB : ∀ v∈B, (∃ u, G.Adj u v) → v∈A ∨ ∃ u∈K, G.Adj u v) :
    boundaryOn G Finset.univ (J∪K)⊆A := by
  intro v hv
  obtain ⟨u,he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
  have hu : u∈(J∪K).filter (fun u' => G.Adj u' v) := by rw [he]; simp
  have huv := (Finset.mem_filter.mp hu).2
  by_cases huK : u∈K
  · apply hK
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G K (J∪K) v u
      Finset.subset_union_right he huK,Finset.card_singleton]
  · have huJ : u∈J := (Finset.mem_union.mp (Finset.mem_filter.mp hu).1).resolve_right huK
    have hvJ : v∈boundaryOn G Finset.univ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      rw [P2MProofComplexity.P2MBoundaryUnion.filter_singleton_of_subset G J (J∪K) v u
        Finset.subset_union_left he huJ,Finset.card_singleton]⟩
    rcases hB v (hJ hvJ) ⟨u,huv⟩ with hvA | ⟨u',hu'K,hu'v⟩
    · exact hvA
    · have hu' : u'∈(J∪K).filter (fun a => G.Adj a v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hu'K,hu'v⟩
      rw [he] at hu'
      have heq : u'=u := Finset.mem_singleton.mp hu'
      subst u'
      exact (huK hu'K).elim

theorem support_subset (G : BipGraph L R) (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp G s c)
    (A B : Finset R) (hA : (A.card : ℝ) ≤ c*s/2) (hBsize : (B.card : ℝ) ≤ c*s/2)
    (hB : ∀ v∈B, (∃ u, G.Adj u v) → v∈A ∨ ∃ u∈supS G s A, G.Adj u v) :
    supS G s B⊆supS G s A := by
  have hSA := P2MExpansionSmallSupports.properties G s c hc hexp A hA
  have hSB := P2MExpansionSmallSupports.properties G s c hc hexp B hBsize
  have hbdry := boundary_control G (supS G s B) (supS G s A) A B hSB.1 hSA.1 hB
  have hcard : (((supS G s B)∪(supS G s A)).card : ℝ) ≤ s := by
    have hu : (((supS G s B)∪(supS G s A)).card : ℝ) ≤
        ((supS G s B).card : ℝ)+((supS G s A).card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
    have ha := hSA.2.1.trans hSA.2.2
    have hb := hSB.2.1.trans hSB.2.2
    linarith
  exact Finset.subset_union_left.trans (P2MExpansionSupportWitness.contains G s A _ hcard hbdry)

end SemAC02.Supplement.P2MExpansionSupportClosure
end

section
-- Inlined Solutions.P2MExpansionMultiplicationSupport

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionMultiplicationSupport

open MvPolynomial AC02Frege P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem support_subset (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (t.card : ℝ)+1 ≤ c*s/2)
    (d : σ →₀ ℕ) (hd : d∈(expOp P m s t).support) (x : σ) :
    supS P.graph s ((insert x d.support).image P.cluster)⊆
      supS P.graph s ((insert x t).image P.cluster) := by
  let A := (insert x t).image P.cluster
  let B := (insert x d.support).image P.cluster
  have hdt := P2MExpansionMonomialNormalForms.support_card P m hm s t d hd
  have hAnat : A.card ≤ t.card+1 :=
    Finset.card_image_le.trans (Finset.card_insert_le _ _)
  have hBnat : B.card ≤ t.card+1 :=
    Finset.card_image_le.trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hdt 1))
  have hA : (A.card : ℝ) ≤ c*s/2 := by
    have hh : (A.card : ℝ) ≤ (t.card : ℝ)+1 := by exact_mod_cast hAnat
    exact hh.trans hbudget
  have hB : (B.card : ℝ) ≤ c*s/2 := by
    have hh : (B.card : ℝ) ≤ (t.card : ℝ)+1 := by exact_mod_cast hBnat
    exact hh.trans hbudget
  apply P2MExpansionSupportClosure.support_subset P.graph s c hc hexp A B hA hB
  intro v hv hactive
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
  rcases Finset.mem_insert.mp hy with rfl | hy
  · left
    exact Finset.mem_image.mpr ⟨y,Finset.mem_insert_self _ _,rfl⟩
  · obtain ⟨u,hu⟩ := hactive
    have hyv : y∈(expOp P m s t).vars := (mem_vars_iff_mem_support _).mpr ⟨d,hd,hy⟩
    rcases P2MExpansionMonomialNormalForms.active_locality P hP hml m hm s t y hyv u hu with ⟨u',hu',hu'v⟩ | hyA
    · right
      refine ⟨u',?_,hu'v⟩
      exact P2MExpansionSupportWitness.monotone P.graph s (t.image P.cluster) A
        (Finset.image_subset_image (Finset.subset_insert x t)) hu'
    · left
      exact Finset.image_subset_image (Finset.subset_insert x t) hyA

theorem local_reduction (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (t.card : ℝ)+1 ≤ c*s/2)
    (d : σ →₀ ℕ) (hd : d∈(expOp P m s t).support) (x : σ) :
    expOp P m s (insert x d.support)=
      nf m (axioms P (supS P.graph s ((insert x t).image P.cluster))) (xMon (insert x d.support)) := by
  have hdt := P2MExpansionMonomialNormalForms.support_card P m hm s t d hd
  have hA : (((insert x t).image P.cluster).card : ℝ) ≤ c*s/2 := by
    have hh : ((insert x t).image P.cluster).card ≤ t.card+1 :=
      Finset.card_image_le.trans (Finset.card_insert_le _ _)
    have hhR : (((insert x t).image P.cluster).card : ℝ) ≤ (t.card : ℝ)+1 := by exact_mod_cast hh
    exact hhR.trans hbudget
  have hB : (((insert x d.support).image P.cluster).card : ℝ) ≤ c*s/2 := by
    have hh : ((insert x d.support).image P.cluster).card ≤ t.card+1 :=
      Finset.card_image_le.trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hdt 1))
    have hhR : (((insert x d.support).image P.cluster).card : ℝ) ≤ (t.card : ℝ)+1 := by exact_mod_cast hh
    exact hhR.trans hbudget
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp ((insert x t).image P.cluster) hA
  have hsize : ((supS P.graph s ((insert x t).image P.cluster)).card : ℝ) ≤ s := by
    have hh := hProps.2.1.trans hProps.2.2
    have hs : 0 ≤ s := by have hcA := Nat.cast_nonneg (α:=ℝ) ((insert x t).image P.cluster).card; nlinarith
    linarith
  exact (P2MExpansionNormalFormLocality.locality P hP hml m hm s c hc hexp (insert x d.support) hB _
    (support_subset P hP hml m hm s c hc hexp t hbudget d hd x) hsize).symm

end SemAC02.Supplement.P2MExpansionMultiplicationSupport
end

section
-- Inlined Solutions.P2MExpansionLinearMap

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionLinearMap

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

noncomputable def operator (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  (basisMonomials σ (ZMod 2)).constr (ZMod 2) (fun d => expOp P m s d.support)

theorem monomial (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (d : σ →₀ ℕ) (a : ZMod 2) : operator P m s (MvPolynomial.monomial d a)=a • expOp P m s d.support := by
  have h := (basisMonomials σ (ZMod 2)).constr_basis (ZMod 2)
    (fun d => expOp P m s d.support) d
  have ha : MvPolynomial.monomial d a=a • MvPolynomial.monomial d (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  rw [ha,map_smul]
  exact congrArg (fun p => a • p) h

theorem xMon (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ) :
    operator P m s (AC02Frege.xMon t)=expOp P m s t := by
  rw [xMon_eq_monomial,monomial,one_smul,indicator_support]

theorem multilinear (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (p : MvPolynomial σ (ZMod 2)) : IsMultilinear (operator P m s p) := by
  classical
  apply (mem_restrictDegree σ _ 1).mp
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [monomial]
  apply Submodule.smul_mem
  exact (mem_restrictDegree σ _ 1).mpr (P2MExpansionMonomialNormalForms.multilinear P m hm s _)

theorem degree (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (p : MvPolynomial σ (ZMod 2)) : (operator P m s p).totalDegree ≤ p.totalDegree := by
  classical
  have he : operator P m s p=∑ d∈p.support, operator P m s (MvPolynomial.monomial d (coeff d p)) := by
    exact congrArg (operator P m s) p.as_sum |>.trans (map_sum _ _ _)
  apply (mem_restrictTotalDegree σ _ _).mp
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  rw [monomial]
  apply (mem_restrictTotalDegree σ _ _).mpr
  apply (totalDegree_smul_le _ _).trans
  apply (P2MExpansionMonomialNormalForms.degree P m hm s d.support).trans
  apply le_trans _ (le_totalDegree hd)
  change d.support.card ≤ ∑ i∈d.support, d i
  calc
    d.support.card = ∑ _i∈d.support, 1 := by simp
    _ ≤ ∑ i∈d.support, d i := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem ml (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (p : MvPolynomial σ (ZMod 2)) : operator P m s (ML p)=operator P m s p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a => rw [ml_monomial,monomial,monomial,sqfree_support]
  | add p q hp hq => simp only [map_add,hp,hq]

end SemAC02.Supplement.P2MExpansionLinearMap
end

section
-- Inlined Solutions.P2MBooleanNormalFormAlgebra

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormAlgebra

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed P2MBooleanIdealNormalForm

variable {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G : Set (MvPolynomial σ (ZMod 2)))

include hm

theorem congruent (p q : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hq : IsMultilinear q)
    (hpq : p-q∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : nf m G p=nf m G q := by
  have hnp := spec m hm G p hp
  have hnq := spec m hm G q hq
  apply unique m G p _ _ hnp.1 hnq.1 hnp.2.1
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).add_mem hpq hnq.2.1 using 1 <;> ring

theorem zero : nf m G 0=0 := by
  have hml : IsMultilinear (0 : MvPolynomial σ (ZMod 2)) := by intro s hs; simp at hs
  have hs := spec m hm G 0 hml
  apply unique m G 0 _ 0 hs.1 (normalSpan m G).zero_mem hs.2.1
  simp

theorem of_ideal (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hI : p∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})) : nf m G p=0 := by
  have hz : IsMultilinear (0 : MvPolynomial σ (ZMod 2)) := by intro d hd; simp at hd
  have he : p-0∈Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) := by simpa using hI
  exact (congruent m hm G p 0 hp hz he).trans (zero m hm G)

theorem add (p q : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hq : IsMultilinear q) :
    nf m G (p+q)=nf m G p+nf m G q := by
  have hpM := (mem_restrictDegree σ p 1).mpr hp
  have hqM := (mem_restrictDegree σ q 1).mpr hq
  have hs := spec m hm G (p+q) ((mem_restrictDegree σ _ 1).mp
    ((restrictDegree σ (ZMod 2) 1).add_mem hpM hqM))
  have hnp := spec m hm G p hp
  have hnq := spec m hm G q hq
  apply unique m G (p+q) _ _ hs.1 ((normalSpan m G).add_mem hnp.1 hnq.1) hs.2.1
  convert (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).add_mem hnp.2.1 hnq.2.1 using 1 <;> ring

theorem scalar (a : ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G (a • p)=a • nf m G p := by
  have hpM := (mem_restrictDegree σ p 1).mpr hp
  have hs := spec m hm G (a • p) ((mem_restrictDegree σ _ 1).mp
    ((restrictDegree σ (ZMod 2) 1).smul_mem a hpM))
  have hnp := spec m hm G p hp
  apply unique m G (a • p) _ _ hs.1 ((normalSpan m G).smul_mem a hnp.1) hs.2.1
  have hh := (Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_left (C a) hnp.2.1
  simpa only [smul_eq_C_mul,mul_sub] using hh

theorem nested (H : Set (MvPolynomial σ (ZMod 2))) (hGH : G⊆H)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m H (nf m G p)=nf m H p := by
  have hs := spec m hm G p hp
  apply congruent m hm H _ p (normal_multilinear m G _ hs.1) hp
  have hI : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤
      Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i}) :=
    Ideal.span_mono (Set.union_subset_union_left _ hGH)
  have hh := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).neg_mem (hI hs.2.1)
  simpa only [neg_sub] using hh

theorem sum {ι : Type} (S : Finset ι) (p : ι → MvPolynomial σ (ZMod 2))
    (hp : ∀ i∈S, IsMultilinear (p i)) : nf m G (∑ i∈S, p i)=∑ i∈S, nf m G (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,zero m hm G]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,add m hm G _ _ (hp i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]
    · apply (mem_restrictDegree σ _ 1).mp
      exact Submodule.sum_mem _ (fun j hj => (mem_restrictDegree σ _ 1).mpr (hp j (Finset.mem_insert_of_mem hj)))

theorem expansion (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m G p=∑ d∈p.support, coeff d p • nf m G (xMon d.support) := by
  classical
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => AC02Frege.P2MBooleanBasis.squarefree_monomial d _ (hp d hd)))
  calc
    nf m G p = nf m G (∑ d∈p.support, coeff d p • xMon d.support) := congrArg (nf m G) he
    _ = ∑ d∈p.support, nf m G (coeff d p • xMon d.support) := sum m hm G _ _ (fun d _ =>
      (mem_restrictDegree σ _ 1).mp ((restrictDegree σ (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree σ _ 1).mpr (AC02Frege.P2MBooleanAlgebra.xMon_multilinear _))))
    _ = _ := Finset.sum_congr rfl (fun d _ => scalar m hm G _ _ (AC02Frege.P2MBooleanAlgebra.xMon_multilinear _))

end SemAC02.Supplement.P2MBooleanNormalFormAlgebra
end

section
-- Inlined Solutions.P2MBooleanVariableProducts

namespace AC02Frege.P2MBooleanVariableProducts

open MvPolynomial AC02Frege.P2MBooleanAlgebra

theorem monomial_insert {σ : Type} [Finite σ] [DecidableEq σ] (x : σ) (t : Finset σ) :
    ML (X x*xMon t)=xMon (insert x t) := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear _)
  intro y
  simp only [eval_ml,map_mul,eval_X,xMon_eval]
  by_cases hx : x∈t
  · rw [Finset.insert_eq_of_mem hx]
    have he : t=insert x (t.erase x) := (Finset.insert_erase hx).symm
    rw [he,Finset.prod_insert (Finset.notMem_erase x t)]
    have hy : y x*y x=y x := by
      rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (y x) with h | h <;> simp [h]
    rw [←mul_assoc,hy]
  · rw [Finset.prod_insert hx]

end AC02Frege.P2MBooleanVariableProducts
end

section
-- Inlined Solutions.P2MExpansionPolynomialLocality

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionPolynomialLocality

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem eq_nf (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hlocal : ∀ d∈p.support, expOp P m s d.support=nf m G (xMon d.support)) :
    P2MExpansionLinearMap.operator P m s p=nf m G p := by
  classical
  have he := congrArg (P2MExpansionLinearMap.operator P m s) p.as_sum
  rw [map_sum] at he
  rw [he,P2MBooleanNormalFormAlgebra.expansion m hm G p hp]
  exact Finset.sum_congr rfl (fun d hd => by rw [P2MExpansionLinearMap.monomial,hlocal d hd])

theorem variable_sum (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (x : σ) :
    P2MExpansionLinearMap.operator P m s (ML (X x*p))=
      ∑ d∈p.support, coeff d p • expOp P m s (insert x d.support) := by
  classical
  let M := P2MExpansionLinearMap.operator P m s |>.comp (ML.comp (LinearMap.mulLeft (ZMod 2) (X x)))
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => squarefree_monomial d _ (hp d hd)))
  have hh := congrArg M he
  rw [map_sum] at hh
  dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_smul_comm,map_smul,map_smul]
  rw [AC02Frege.P2MBooleanVariableProducts.monomial_insert,P2MExpansionLinearMap.xMon]

theorem variable_eq_nf (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (x : σ)
    (hlocal : ∀ d∈p.support, expOp P m s (insert x d.support)=nf m G (xMon (insert x d.support))) :
    P2MExpansionLinearMap.operator P m s (ML (X x*p))=nf m G (ML (X x*p)) := by
  classical
  rw [variable_sum P m s p hp x]
  let M := ML.comp (LinearMap.mulLeft (ZMod 2) (X x))
  have he : p=∑ d∈p.support, coeff d p • xMon d.support :=
    p.as_sum.trans (Finset.sum_congr rfl (fun d hd => squarefree_monomial d _ (hp d hd)))
  have hh := congrArg M he
  rw [map_sum] at hh
  have hsum : ML (X x*p)=∑ d∈p.support, coeff d p • xMon (insert x d.support) := by
    dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
    exact hh.trans (Finset.sum_congr rfl (fun d _ => by
      rw [mul_smul_comm,map_smul]
      rw [AC02Frege.P2MBooleanVariableProducts.monomial_insert]))
  rw [hsum,P2MBooleanNormalFormAlgebra.sum m hm G]
  · exact Finset.sum_congr rfl (fun d hd => (congrArg (fun q => coeff d p • q) (hlocal d hd)).trans
      (P2MBooleanNormalFormAlgebra.scalar m hm G _ _ (xMon_multilinear _)).symm)
  · intro d hd
    exact (mem_restrictDegree σ _ 1).mp ((restrictDegree σ (ZMod 2) 1).smul_mem _
      ((mem_restrictDegree σ _ 1).mpr (xMon_multilinear _)))

end SemAC02.Supplement.P2MExpansionPolynomialLocality
end

section
-- Inlined Solutions.P2MBooleanNormalFormMultiplication

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBooleanNormalFormMultiplication

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

theorem nested_product {σ : Type} (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (G H : Set (MvPolynomial σ (ZMod 2))) (hGH : G⊆H)
    (f p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) :
    nf m H (ML (f*nf m G p))=nf m H (ML (f*p)) := by
  apply P2MBooleanNormalFormAlgebra.congruent m hm H _ _ (ml_multilinear _) (ml_multilinear _)
  rw [←map_sub]
  have hI : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤
      Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i}) :=
    Ideal.span_mono (Set.union_subset_union_left _ hGH)
  have hdiff := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).neg_mem
    (hI (P2MBooleanIdealNormalForm.spec m hm G p hp).2.1)
  have hprod := (Ideal.span (H ∪ {p | ∃ i : σ, p=X i^2-X i})).mul_mem_left f hdiff
  apply AC02Frege.P2MBooleanIdealMultilinearization.closed
  convert hprod using 1 <;> ring

end SemAC02.Supplement.P2MBooleanNormalFormMultiplication
end

section
-- Inlined Solutions.P2MExpansionMultiplicationIdentity

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionMultiplicationIdentity

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem monomial (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (t.card : ℝ)+1 ≤ c*s/2) (x : σ) :
    P2MExpansionLinearMap.operator P m s (ML (X x*expOp P m s t))=expOp P m s (insert x t) := by
  let J := supS P.graph s (t.image P.cluster)
  let K := supS P.graph s ((insert x t).image P.cluster)
  have hJK : J⊆K := P2MExpansionSupportWitness.monotone P.graph s _ _
    (Finset.image_subset_image (Finset.subset_insert x t))
  have he := P2MExpansionPolynomialLocality.variable_eq_nf P m hm s (axioms P K)
    (expOp P m s t) (P2MExpansionMonomialNormalForms.multilinear P m hm s t) x
    (fun d hd => P2MExpansionMultiplicationSupport.local_reduction P hP hml m hm s c hc hexp t hbudget d hd x)
  rw [he]
  change nf m (axioms P K) (ML (X x*nf m (axioms P J) (xMon t)))=_
  rw [P2MBooleanNormalFormMultiplication.nested_product m hm _ _ (axioms_mono P J K hJK) _ _ (xMon_multilinear t),
    AC02Frege.P2MBooleanVariableProducts.monomial_insert]
  rfl

theorem polynomial (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hbudget : (p.totalDegree : ℝ)+1 ≤ c*s/2) (x : σ) :
    P2MExpansionLinearMap.operator P m s (ML (X x*P2MExpansionLinearMap.operator P m s p))=
      P2MExpansionLinearMap.operator P m s (ML (X x*p)) := by
  classical
  let M := P2MExpansionLinearMap.operator P m s |>.comp (ML.comp (LinearMap.mulLeft (ZMod 2) (X x)))
  have he : P2MExpansionLinearMap.operator P m s p=
      ∑ d∈p.support, coeff d p • expOp P m s d.support := by
    have hh := congrArg (P2MExpansionLinearMap.operator P m s) p.as_sum
    rw [map_sum] at hh
    exact hh.trans (Finset.sum_congr rfl (fun d _ => P2MExpansionLinearMap.monomial P m s d _))
  have hh := congrArg M he
  rw [map_sum] at hh
  dsimp only [M,LinearMap.comp_apply,LinearMap.mulLeft_apply] at hh
  rw [hh,P2MExpansionPolynomialLocality.variable_sum P m s p hp x]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_smul_comm,map_smul,map_smul]
  have hcard : d.support.card ≤ p.totalDegree := by
    rw [←AC02Frege.P2MBooleanBasis.squarefree_sum d (hp d hd)]
    exact le_totalDegree hd
  have hcardR : (d.support.card : ℝ) ≤ p.totalDegree := by exact_mod_cast hcard
  rw [monomial P hP hml m hm s c hc hexp d.support (by linarith) x]

end SemAC02.Supplement.P2MExpansionMultiplicationIdentity
end

section
-- Inlined Solutions.P2MExpansionBackgroundCompatibility

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionBackgroundCompatibility

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem monomial (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (t : Finset σ) (hbudget : (t.card : ℝ) ≤ c*s/2) :
    P2MExpansionLinearMap.operator P m s (nf m (axioms P ∅) (xMon t))=expOp P m s t := by
  let A := t.image P.cluster
  let J := supS P.graph s A
  let q := nf m (axioms P ∅) (xMon t)
  have hq := P2MBooleanIdealNormalForm.spec m hm (axioms P ∅) (xMon t) (xMon_multilinear t)
  have hqml : IsMultilinear q := P2MExpansionNormalFormFixed.normal_multilinear m _ _ hq.1
  have hqdeg : q.totalDegree ≤ t.card := hq.2.2.trans_eq (xMon_totalDegree t)
  have hA : (A.card : ℝ) ≤ c*s/2 := by
    have hh : (A.card : ℝ) ≤ t.card := by exact_mod_cast Finset.card_image_le
    exact hh.trans hbudget
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp A hA
  have hs : 0 ≤ s := by have hz := Nat.cast_nonneg (α:=ℝ) t.card; nlinarith
  have hJs : (J.card : ℝ) ≤ s := by have hh := hProps.2.1.trans hProps.2.2; dsimp [J]; linarith
  have hlocal : ∀ d∈q.support, expOp P m s d.support=nf m (axioms P J) (xMon d.support) := by
    intro d hd
    let B := d.support.image P.cluster
    have hcard : d.support.card ≤ t.card := by
      rw [←squarefree_sum d (hqml d hd)]
      exact (le_totalDegree hd).trans hqdeg
    have hB : (B.card : ℝ) ≤ c*s/2 := by
      have hh : B.card ≤ t.card := Finset.card_image_le.trans hcard
      have hhR : (B.card : ℝ) ≤ t.card := by exact_mod_cast hh
      exact hhR.trans hbudget
    have hSJ : supS P.graph s B⊆J := by
      apply P2MExpansionSupportClosure.support_subset P.graph s c hc hexp A B hA hB
      intro v hv hactive
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u,hu⟩ := hactive
      have hxq : x∈q.vars := (mem_vars_iff_mem_support _).mpr ⟨d,hd,hx⟩
      rcases P2MClusterNormalFormVariables.active_locality P hP hml m hm ∅ t x hxq u hu with ⟨u',hu',_⟩ | hinput
      · simp at hu'
      · exact Or.inl hinput
    exact (P2MExpansionNormalFormLocality.locality P hP hml m hm s c hc hexp d.support hB J hSJ hJs).symm
  rw [P2MExpansionPolynomialLocality.eq_nf P m hm s (axioms P J) q hqml hlocal]
  exact P2MBooleanNormalFormAlgebra.nested m hm (axioms P ∅) (axioms P J)
    (axioms_mono P ∅ J (Finset.empty_subset J)) (xMon t) (xMon_multilinear t)

theorem polynomial (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p)
    (hbudget : (p.totalDegree : ℝ) ≤ c*s/2) :
    P2MExpansionLinearMap.operator P m s (nf m (axioms P ∅) p)=P2MExpansionLinearMap.operator P m s p := by
  classical
  rw [P2MBooleanNormalFormAlgebra.expansion m hm (axioms P ∅) p hp,map_sum]
  have he := congrArg (P2MExpansionLinearMap.operator P m s) p.as_sum
  rw [map_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul,P2MExpansionLinearMap.monomial]
  have hcard : d.support.card ≤ p.totalDegree := by
    rw [←squarefree_sum d (hp d hd)]
    exact le_totalDegree hd
  have hcardR : (d.support.card : ℝ) ≤ p.totalDegree := by exact_mod_cast hcard
  rw [monomial P hP hml m hm s c hc hexp d.support (hcardR.trans hbudget)]

end SemAC02.Supplement.P2MExpansionBackgroundCompatibility
end

section
-- Inlined Solutions.P2MRestrictionLeadingMonomial

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRestrictionLeadingMonomial

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MBooleanNormalFormRestrictions

variable {σ : Type} [DecidableEq σ]

lemma filtered_indicator_le (e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (keep : σ → Prop) [DecidablePred keep] :
    Finsupp.indicator (e.support.filter keep) (fun _ _ => 1) ≤ e := by
  intro x
  by_cases hx : x∈e.support.filter keep
  · have hs := (Finset.mem_filter.mp hx).1
    have hp := Finsupp.mem_support_iff.mp hs
    simp only [Finsupp.indicator_apply,dif_pos hx]
    omega
  · simp only [Finsupp.indicator_apply,dif_neg hx]
    exact Nat.zero_le _

lemma coeff_zero (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (d e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (hnot : ¬ d ≤ e) (a : ZMod 2) :
    coeff d (restrict keep α (MvPolynomial.monomial e a))=0 := by
  rw [squarefree_monomial e a he,map_smul,P2MBooleanNormalFormRestrictions.monomial,xMon_eq_monomial]
  rw [smul_smul,smul_monomial]
  rw [MvPolynomial.coeff_monomial]
  split_ifs with hd
  · exfalso
    apply hnot
    rw [←hd]
    exact filtered_indicator_le e he keep
  · rfl

lemma monomial_fixed (keep : σ → Prop) [DecidablePred keep] (α : σ → ZMod 2)
    (e : σ →₀ ℕ) (he : ∀ x, e x ≤ 1) (hkeep : ∀ x∈e.support, keep x) (a : ZMod 2) :
    restrict keep α (MvPolynomial.monomial e a)=MvPolynomial.monomial e a := by
  rw [squarefree_monomial e a he,map_smul,P2MBooleanNormalFormRestrictions.monomial]
  have hfilter : e.support.filter keep=e.support := Finset.filter_eq_self.mpr hkeep
  have hnone : e.support.filter (fun x => ¬ keep x)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_filter.mp hx).2 (hkeep x (Finset.mem_filter.mp hx).1)
  rw [hnone,Finset.prod_empty,one_smul,hfilter]

theorem coeff_leading (m : MonomialOrder σ) (keep : σ → Prop) [DecidablePred keep]
    (α : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hn : p≠0)
    (hkeep : ∀ x∈(m.degree p).support, keep x) :
    coeff (m.degree p) (restrict keep α p)=coeff (m.degree p) p := by
  classical
  have hsum : restrict keep α p=∑ e∈p.support, restrict keep α (MvPolynomial.monomial e (coeff e p)) := by
    simpa only [map_sum] using congrArg (restrict keep α) p.as_sum
  rw [hsum,coeff_sum]
  rw [Finset.sum_eq_single (m.degree p)]
  · rw [monomial_fixed keep α (m.degree p) (hp _ (m.degree_mem_support hn)) hkeep]
    simp [coeff_monomial]
  · intro e he hne
    apply coeff_zero keep α (m.degree p) e (hp e he)
    intro hle
    have heq : m.degree p=e := m.toSyn.injective (le_antisymm (m.toSyn_monotone hle) (m.le_degree he))
    exact hne heq.symm
  · intro hnot
    exact (hnot (m.degree_mem_support hn)).elim

theorem nonzero (m : MonomialOrder σ) (keep : σ → Prop) [DecidablePred keep]
    (α : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) (hp : IsMultilinear p) (hn : p≠0)
    (hkeep : ∀ x∈(m.degree p).support, keep x) : restrict keep α p≠0 := by
  intro hz
  have hcoeff := coeff_leading m keep α p hp hn hkeep
  rw [hz,MvPolynomial.coeff_zero] at hcoeff
  exact (m.coeff_degree_ne_zero_iff.mpr hn) hcoeff.symm

end SemAC02.Supplement.P2MRestrictionLeadingMonomial
end

section
-- Inlined Solutions.P2MRespectfulAxiomSupport

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRespectfulAxiomSupport

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [DecidableEq R]

theorem leading_covers (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.Fu u) (hn : p≠0)
    (v : R) (huv : P.graph.Adj u v) : v∈(m.degree p).support.image P.cluster := by
  obtain ⟨α,hFu,hF0⟩ := P2MRespectfulPolynomialAssignment.assignment P hP hml {u} v u (by simp [huv])
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
  by_contra hnot
  have hkeep : ∀ x∈(m.degree p).support, P.cluster x≠v := by
    intro x hx he
    exact hnot (Finset.mem_image.mpr ⟨x,hx,he⟩)
  have hpin := P2MRestrictionLeadingMonomial.nonzero m (fun x => P.cluster x≠v) α p hpml hn hkeep
  have hz := hFu p hp
  rw [P2MClusterRestrictionBasics.as_restriction] at hz
  exact hpin hz

theorem witness (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.Fu u) (hn : p≠0) :
    ∃ t : Finset σ, t.card ≤ p.totalDegree ∧
      (∀ v : R, P.graph.Adj u v → v∈t.image P.cluster) ∧
      (∀ x∈p.vars, P.cluster x∈t.image P.cluster) := by
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
  refine ⟨(m.degree p).support,?_,leading_covers P hP hml m u p hp hn,?_⟩
  · rw [←squarefree_sum (m.degree p) (hpml _ (m.degree_mem_support hn))]
    exact le_totalDegree (m.degree_mem_support hn)
  · intro x hx
    exact leading_covers P hP hml m u p hp hn (P.cluster x) ⟨p,hp,x,hx,rfl⟩

end SemAC02.Supplement.P2MRespectfulAxiomSupport
end

section
-- Inlined Solutions.P2MExpansionAxiomAnnihilation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionAxiomAnnihilation

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem left_axiom (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (u : L) (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.Fu u)
    (hbudget : (p.totalDegree : ℝ) ≤ c*s/2) : P2MExpansionLinearMap.operator P m s p=0 := by
  by_cases hn : p=0
  · rw [hn,map_zero]
  obtain ⟨t,ht,hneighbors,hvars⟩ := P2MRespectfulAxiomSupport.witness P hP hml m u p hp hn
  let A := t.image P.cluster
  let J := supS P.graph s A
  have hA : (A.card : ℝ) ≤ c*s/2 := by
    have hh : A.card ≤ p.totalDegree := Finset.card_image_le.trans ht
    have hhR : (A.card : ℝ) ≤ p.totalDegree := by exact_mod_cast hh
    exact hhR.trans hbudget
  have hProps := P2MExpansionSmallSupports.properties P.graph s c hc hexp A hA
  have hJs : (J.card : ℝ) ≤ s := by have hh := hProps.2.1.trans hProps.2.2; dsimp [J]; linarith
  have hu : u∈J := by
    apply P2MExpansionSupportWitness.contains P.graph s A {u} (by simpa using hs) _ (Finset.mem_singleton_self u)
    intro v hv
    have hfilter : ({u} : Finset L).filter (fun a => P.graph.Adj a v)≠∅ := by
      intro he
      have hh := (Finset.mem_filter.mp hv).2
      rw [he,Finset.card_empty] at hh
      omega
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hfilter
    have hau : a=u := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
    exact hneighbors v (hau ▸ (Finset.mem_filter.mp ha).2)
  have hpml : IsMultilinear p := hml p (Or.inr ⟨u,hp⟩)
  have hlocal : ∀ d∈p.support, expOp P m s d.support=nf m (axioms P J) (xMon d.support) := by
    intro d hd
    have hBsub : d.support.image P.cluster⊆A := by
      rintro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact hvars x ((mem_vars_iff_mem_support _).mpr ⟨d,hd,hx⟩)
    have hB : ((d.support.image P.cluster).card : ℝ) ≤ c*s/2 := by
      have hh : ((d.support.image P.cluster).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBsub
      exact hh.trans hA
    exact (P2MExpansionNormalFormLocality.locality P hP hml m hm s c hc hexp d.support hB J
      (P2MExpansionSupportWitness.monotone P.graph s _ A hBsub) hJs).symm
  rw [P2MExpansionPolynomialLocality.eq_nf P m hm s (axioms P J) p hpml hlocal]
  exact P2MBooleanNormalFormAlgebra.of_ideal m hm (axioms P J) p hpml
    (Ideal.subset_span (Or.inl (Or.inr ⟨u,hu,hp⟩)))

theorem background_axiom (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (p : MvPolynomial σ (ZMod 2)) (hp : p∈P.F0)
    (hbudget : (p.totalDegree : ℝ) ≤ c*s/2) : P2MExpansionLinearMap.operator P m s p=0 := by
  have hpml : IsMultilinear p := hml p (Or.inl hp)
  rw [←P2MExpansionBackgroundCompatibility.polynomial P hP hml m hm s c hc hexp p hpml hbudget,
    P2MBooleanNormalFormAlgebra.of_ideal m hm (axioms P ∅) p hpml
      (Ideal.subset_span (Or.inl (Or.inl hp))),map_zero]

end SemAC02.Supplement.P2MExpansionAxiomAnnihilation
end

section
-- Inlined Solutions.P2MBackgroundNormalFormOne

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBackgroundNormalFormOne

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

theorem irreducible {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (hzero : ∃ y : σ → Bool, ∀ g∈G, eval (toF2 y) g=0) : IsIrred m G ∅ := by
  obtain ⟨y,hy⟩ := hzero
  have hvanish : Ideal.span (G ∪ {p | ∃ i : σ, p=X i^2-X i}) ≤ RingHom.ker (eval (toF2 y)) := by
    apply Ideal.span_le.mpr
    intro p hp
    change eval (toF2 y) p=0
    rcases hp with hp | ⟨i,rfl⟩
    · exact hy p hp
    · cases hi : y i <;> simp [map_sub,map_pow,toF2,hi]
  intro q hq hn he
  have hdeg : m.degree q=0 := by simpa [xMon] using he
  have hconst := m.degree_eq_zero_iff.mp hdeg
  have hc := AC02Frege.P2MLinearStandardMonomials.leadingCoeff_one m hn
  have hqzero : eval (toF2 y) q=0 := hvanish hq.2
  rw [hconst,hc,eval_C] at hqzero
  exact one_ne_zero hqzero

theorem fixed {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (hzero : ∃ y : σ → Bool, ∀ g∈G, eval (toF2 y) g=0) : nf m G 1=1 := by
  simpa only [xMon,Finset.prod_empty] using P2MExpansionNormalFormFixed.nf_fixed m G ∅ (irreducible m G hzero)

end SemAC02.Supplement.P2MBackgroundNormalFormOne
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
-- Inlined Solutions.P2MExpansionPseudoReduction

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionPseudoReduction

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

noncomputable def reduction (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (K : ℕ) :
    Ble σ K →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  (P2MExpansionLinearMap.operator P m s).comp (Ble σ K).subtype

theorem pseudo (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hK : (K : ℝ)+1 ≤ c*s/2) : IsPseudoRed P.axioms (reduction P m s K) := by
  constructor
  · intro p hp hpK
    have hdeg := ((P2MBooleanDegreeSpaces.mem_Ble_iff K p).mp hpK).2
    have hbudget : (p.totalDegree : ℝ) ≤ c*s/2 := by
      have hh : (p.totalDegree : ℝ) ≤ K := by exact_mod_cast hdeg
      linarith
    rcases hp with hp | ⟨u,hp⟩
    · exact P2MExpansionAxiomAnnihilation.background_axiom P hP hml m hm s c hc hexp p hp hbudget
    · exact P2MExpansionAxiomAnnihilation.left_axiom P hP hml m hm s c hs hc hexp u p hp hbudget
  · intro p x hx hz
    have hp := (P2MBooleanDegreeSpaces.mem_Ble_iff K (p : MvPolynomial σ (ZMod 2))).mp p.2
    have hbudget : ((p : MvPolynomial σ (ZMod 2)).totalDegree : ℝ)+1 ≤ c*s/2 := by
      have hh : (((p : MvPolynomial σ (ZMod 2)).totalDegree : ℝ)) ≤ K := by exact_mod_cast hp.2
      linarith
    change P2MExpansionLinearMap.operator P m s (ML (X x*(p : MvPolynomial σ (ZMod 2))))=0
    change P2MExpansionLinearMap.operator P m s (p : MvPolynomial σ (ZMod 2))=0 at hz
    rw [←P2MExpansionMultiplicationIdentity.polynomial P hP hml m hm s c hc hexp _ hp.1 hbudget x,hz,mul_zero,map_zero,map_zero]

theorem sup_empty (P : ClusteredRep σ L R) (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (hexp : IsBdryExp P.graph s c) : supS P.graph s ∅=∅ := by
  have hbudget : ((∅ : Finset R).card : ℝ) ≤ c*s/2 := by simp only [Finset.card_empty,Nat.cast_zero]; positivity
  have hh := (P2MExpansionSmallSupports.properties P.graph s c hc hexp ∅ hbudget).2.1
  have hz : (supS P.graph s ∅).card=0 := by
    simp only [Finset.card_empty,Nat.cast_zero,zero_div] at hh
    exact_mod_cast (le_antisymm hh (Nat.cast_nonneg (α:=ℝ) _))
  exact Finset.card_eq_zero.mp hz

theorem one (P : ClusteredRep σ L R) (m : MonomialOrder σ)
    (hzero : ∃ y : σ → Bool, ∀ g∈P.F0, eval (toF2 y) g=0)
    (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c) (hexp : IsBdryExp P.graph s c) :
    P2MExpansionLinearMap.operator P m s 1=1 := by
  have he : (1 : MvPolynomial σ (ZMod 2))=xMon ∅ := by simp [AC02Frege.xMon]
  rw [he,P2MExpansionLinearMap.xMon]
  exact P2MExpansionNormalFormFixed.expOp_fixed P m s ∅ (P2MBackgroundNormalFormOne.irreducible m P.F0 hzero)
    (by simpa only [Finset.image_empty] using sup_empty P s c hs hc hexp)

theorem degree (P : ClusteredRep σ L R) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s : ℝ) (K : ℕ) (p : Ble σ K) :
    (reduction P m s K p).totalDegree ≤ (p : MvPolynomial σ (ZMod 2)).totalDegree :=
  P2MExpansionLinearMap.degree P m hm s _

end SemAC02.Supplement.P2MExpansionPseudoReduction
end

section
-- Inlined Solutions.P2MBooleanNormalFormSupport

namespace SemAC02.Supplement.P2MBooleanNormalFormSupport

open MvPolynomial AC02Frege AC02Frege.P2MBooleanBasis P2MExpansionNormalFormFixed

theorem characterization {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) : p∈normalSpan m G ↔
      IsMultilinear p ∧ ∀ d∈p.support, IsIrred m G d.support := by
  have he : normalSpan m G=monomialSpan (IsIrred m G) := by
    unfold normalSpan monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨t,ht,rfl⟩
  rw [he,mem_monomialSpan_iff]

end SemAC02.Supplement.P2MBooleanNormalFormSupport
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
-- Inlined Solutions.P2MExpansionReductionRank

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionReductionRank

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MClusterLocalIdeals

variable {σ L R : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]

theorem image_eq (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (k : ℕ) (hk : (k : ℝ) ≤ c*s/2) :
    (Ble σ k).map (P2MExpansionLinearMap.operator P m s)=
      Submodule.span (ZMod 2) (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k}) := by
  classical
  let U := Submodule.span (ZMod 2) (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k})
  have hbg : axioms P ∅=P.F0 := by ext p; simp [axioms]
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    change P2MExpansionLinearMap.operator P m s (xMon t)∈U
    rw [P2MExpansionLinearMap.xMon]
    have htR : (t.card : ℝ) ≤ c*s/2 := (by exact_mod_cast ht : (t.card : ℝ) ≤ k) |>.trans hk
    rw [←P2MExpansionBackgroundCompatibility.monomial P hP hml m hm s c hc hexp t htR,hbg]
    let q := nf m P.F0 (xMon t)
    have hq := P2MBooleanIdealNormalForm.spec m hm P.F0 (xMon t) (xMon_multilinear t)
    have hchar := (P2MBooleanNormalFormSupport.characterization m P.F0 q).mp hq.1
    have he := congrArg (P2MExpansionLinearMap.operator P m s) q.as_sum
    rw [map_sum] at he
    rw [he]
    apply Submodule.sum_mem
    intro d hd
    rw [P2MExpansionLinearMap.monomial]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨d.support,⟨hchar.2 d hd,?_⟩,rfl⟩
    rw [←squarefree_sum d (hchar.1 d hd)]
    exact (le_totalDegree hd).trans (hq.2.2.trans ((xMon_totalDegree t).le.trans ht))
  · apply Submodule.span_le.mpr
    rintro p ⟨t,⟨ht,hcard⟩,rfl⟩
    exact ⟨xMon t,Submodule.subset_span ⟨t,hcard,rfl⟩,P2MExpansionLinearMap.xMon P m s t⟩

theorem rank_eq (P : ClusteredRep σ L R) (hP : P.IsRespectful)
    (hml : ∀ p∈P.axioms, IsMultilinear p) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (s c : ℝ) (hc : 0 < c) (hexp : IsBdryExp P.graph s c)
    (K k : ℕ) (hkK : k ≤ K) (hk : (k : ℝ) ≤ c*s/2) :
    rankLe (P2MExpansionPseudoReduction.reduction P m s K) k=expRank P m s k := by
  have he : (Submodule.comap (Ble σ K).subtype (Ble σ k)).map (P2MExpansionPseudoReduction.reduction P m s K)=
      (Ble σ k).map (P2MExpansionLinearMap.operator P m s) := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,P2MPseudoReductionRestriction.ble_mono hkK hp⟩,hp,rfl⟩
  unfold rankLe expRank
  rw [he,image_eq P hP hml m hm s c hc hexp k hk]

end SemAC02.Supplement.P2MExpansionReductionRank
end

section
-- Inlined Solutions.P2MExpansionOperatorTheorem

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionOperatorTheorem

open MvPolynomial AC02Frege

theorem full {σ L T : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T]
    (P : ClusteredRep σ L T) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (hml : ∀ p∈P.axioms, IsMultilinear p)
    (hzero : ∃ y : σ → Bool, ∀ g∈P.F0, eval (toF2 y) g=0)
    (hP : P.IsRespectful) (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hexp : IsBdryExp P.graph s c) (K : ℕ)
    (hdeg : ∀ p∈P.axioms, p.totalDegree ≤ K) (hK : (K : ℝ)+1 ≤ c*s/2) :
    ∃ R : Ble σ K →ₗ[ZMod 2] MvPolynomial σ (ZMod 2),
      IsPseudoRed P.axioms R ∧
      (∀ p : Ble σ K, (R p).totalDegree ≤ (p : MvPolynomial σ (ZMod 2)).totalDegree) ∧
      (∀ (t : Finset σ) (ht : t.card ≤ K),
        R ⟨xMon t,Submodule.subset_span ⟨t,ht,rfl⟩⟩=expOp P m s t) ∧
      (∀ k : ℕ, k ≤ K → rankLe R k=expRank P m s k) ∧
      R ⟨xMon ∅,Submodule.subset_span ⟨∅,Nat.zero_le K,rfl⟩⟩=1 := by
  refine ⟨P2MExpansionPseudoReduction.reduction P m s K,
    P2MExpansionPseudoReduction.pseudo P hP hml m hm s c hs hc hexp K hK,
    P2MExpansionPseudoReduction.degree P m hm s K,?_,?_,?_⟩
  · intro t ht
    exact P2MExpansionLinearMap.xMon P m s t
  · intro k hk
    have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk
    exact P2MExpansionReductionRank.rank_eq P hP hml m hm s c hc hexp K k hk (by linarith)
  · change P2MExpansionLinearMap.operator P m s (xMon ∅)=1
    simpa only [AC02Frege.xMon,Finset.prod_empty] using P2MExpansionPseudoReduction.one P m hzero s c (by linarith) hc hexp

end SemAC02.Supplement.P2MExpansionOperatorTheorem
end

end P2MExpansionOperatorProof
open SemAC02 SemAC02.Supplement MvPolynomial AC02Frege

theorem solution {σ L T : Type} [Finite σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype T] [DecidableEq T]
    (P : ClusteredRep σ L T) (m : MonomialOrder σ) (hm : IsDegCompatible m)
    (hml : ∀ p∈P.axioms, IsMultilinear p)
    (hzero : ∃ y : σ → Bool, ∀ g∈P.F0, eval (toF2 y) g=0)
    (hP : P.IsRespectful) (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hexp : IsBdryExp P.graph s c) (K : ℕ)
    (hdeg : ∀ p∈P.axioms, p.totalDegree ≤ K) (hK : (K : ℝ)+1 ≤ c*s/2) :
    ∃ R : Ble σ K →ₗ[ZMod 2] MvPolynomial σ (ZMod 2),
      IsPseudoRed P.axioms R ∧
      (∀ p : Ble σ K, (R p).totalDegree ≤ (p : MvPolynomial σ (ZMod 2)).totalDegree) ∧
      (∀ (t : Finset σ) (ht : t.card ≤ K),
        R ⟨xMon t,Submodule.subset_span ⟨t,ht,rfl⟩⟩=expOp P m s t) ∧
      (∀ k : ℕ, k ≤ K → rankLe R k=expRank P m s k) ∧
      R ⟨xMon ∅,Submodule.subset_span ⟨∅,Nat.zero_le K,rfl⟩⟩=1 := by
  exact P2MExpansionOperatorProof.SemAC02.Supplement.P2MExpansionOperatorTheorem.full P m hm hml hzero hP s c hs hc hexp K hdeg hK
