-- Prove2me | solution 1 for SemAC02.Supplement.theorem_5_4_rank_from_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T08:58:40.212606+00:00
-- url     : https://prove2.me/submissions/574fab99-8a65-44cc-b92f-7bf4bb88a124

import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_nbrOn

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MExpansionRankProof
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
-- Inlined Solutions.P2MExpansionFixedMonomialRank

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionFixedMonomialRank

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MExpansionNormalFormFixed

theorem count {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (k : ℕ)
    (E : Finset (Finset σ))
    (hstd : ∀ t∈E, IsIrred m P.F0 t) (hdeg : ∀ t∈E, t.card ≤ k)
    (hSup : ∀ t∈E, supS P.graph s (t.image P.cluster)=∅) : E.card ≤ expRank P m s k := by
  let U := Submodule.span (ZMod 2) (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k})
  have hfinite : (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k}).Finite :=
    (Set.toFinite _).image _
  letI : Module.Finite (ZMod 2) U := Module.Finite.span_of_finite (ZMod 2) hfinite
  have hmem (t : E) : xMon t.1∈U := by
    rw [←expOp_fixed P m s t.1 (hstd t.1 t.2) (hSup t.1 t.2)]
    exact Submodule.subset_span ⟨t.1,⟨hstd t.1 t.2,hdeg t.1 t.2⟩,rfl⟩
  let b (t : E) : U := ⟨xMon t.1,hmem t⟩
  have hb : LinearIndependent (ZMod 2) b := by
    apply LinearIndependent.of_comp U.subtype
    exact xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  simpa only [Fintype.card_coe,U,expRank] using hb.fintype_card_le_finrank

end SemAC02.Supplement.P2MExpansionFixedMonomialRank
end

section
-- Inlined Solutions.P2MClusterMonomialChoices

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MClusterMonomialChoices

variable {σ R : Type} [Fintype σ] [DecidableEq σ] [Fintype R] [DecidableEq R]

abbrev Choice (cl : σ → R) (A : Finset R) := (v : A) → {x : σ // cl x=v.1}

noncomputable def selected (cl : σ → R) (A : Finset R) (a : Choice cl A) : Finset σ :=
  Finset.univ.image (fun v : A => (a v).1)

lemma selected_injective (cl : σ → R) (A : Finset R) (a : Choice cl A) :
    Function.Injective (fun v : A => (a v).1) := by
  intro v w he
  apply Subtype.ext
  exact (a v).2.symm.trans ((congrArg cl he).trans (a w).2)

theorem selected_card (cl : σ → R) (A : Finset R) (a : Choice cl A) : (selected cl A a).card=A.card := by
  rw [selected,Finset.card_image_of_injective _ (selected_injective cl A a),Finset.card_univ,Fintype.card_coe]

theorem selected_image (cl : σ → R) (A : Finset R) (a : Choice cl A) : (selected cl A a).image cl=A := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    rw [(a w).2]
    exact w.2
  · intro hv
    refine Finset.mem_image.mpr ⟨(a ⟨v,hv⟩).1,?_,(a ⟨v,hv⟩).2⟩
    exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

theorem one_per_cluster (cl : σ → R) (A : Finset R) (a : Choice cl A) :
    ∀ x∈selected cl A a, ∀ y∈selected cl A a, cl x=cl y → x=y := by
  intro x hx y hy he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
  have he' : v=w := Subtype.ext ((a v).2.symm.trans (he.trans (a w).2))
  rw [he']

theorem selected_determines_choice (cl : σ → R) (A : Finset R) (a b : Choice cl A)
    (he : selected cl A a=selected cl A b) : a=b := by
  funext v
  apply Subtype.ext
  have hx : (a v).1∈selected cl A b := by
    rw [←he]
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hx
  have he' : w=v := Subtype.ext ((b w).2.symm.trans ((congrArg cl hwe).trans (a v).2))
  subst w
  exact hwe.symm

theorem choice_card (cl : σ → R) (D : ℕ)
    (hcl : ∀ v : R, (Finset.univ.filter (fun x => cl x=v)).card=D) (A : Finset R) :
    Fintype.card (Choice cl A)=D^A.card := by
  classical
  rw [Fintype.card_pi]
  have hf (v : A) : Fintype.card {x : σ // cl x=v.1}=D := by
    rw [Fintype.card_subtype]
    exact hcl v.1
  simp only [hf,Finset.prod_const,Finset.card_univ,Fintype.card_coe]

theorem sigma_selected_injective (cl : σ → R) (E : Finset (Finset R)) :
    Function.Injective (fun z : (A : E) × Choice cl A.1 => selected cl z.1.1 z.2) := by
  intro z w he
  rcases z with ⟨A,a⟩
  rcases w with ⟨B,b⟩
  have hAB : A=B := Subtype.ext (by
    have hi := congrArg (Finset.image cl) he
    simpa only [selected_image] using hi)
  subst B
  have hab : a=b := selected_determines_choice cl A.1 a b he
  subst b
  rfl

end ProofComplexity.P2MClusterMonomialChoices
end

section
-- Inlined Solutions.P2MBoundaryAvoidance

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBoundaryAvoidance

open PCNonBool

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def Avoiding (G : BipGraph L R) (s : ℝ) (A : Finset R) : Prop :=
  ∀ J : Finset L, J.Nonempty → (J.card : ℝ) ≤ s → ¬ boundaryOn G Finset.univ J⊆A

theorem sup_eq_empty (G : BipGraph L R) (s : ℝ) (A : Finset R) (hA : Avoiding G s A) : supS G s A=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨J,hJ,huJ⟩ := Finset.mem_biUnion.mp hu
  have hh := (Finset.mem_filter.mp hJ).2
  exact hA J ⟨u,huJ⟩ hh.1 hh.2

theorem avoiding_of_sup_empty (G : BipGraph L R) (s : ℝ) (A : Finset R) (hA : supS G s A=∅) :
    Avoiding G s A := by
  classical
  intro J hJ hsize hsub
  obtain ⟨u,hu⟩ := hJ
  have hm : u∈supS G s A := Finset.mem_biUnion.mpr
    ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsize,hsub⟩,hu⟩
  rw [hA] at hm
  simpa using hm

end SemAC02.Supplement.P2MBoundaryAvoidance
end

section
-- Inlined Solutions.P2MExpansionAvoidingRank

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionAvoidingRank

open AC02Frege ProofComplexity.P2MClusterMonomialChoices P2MBoundaryAvoidance

theorem count {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (k D : ℕ)
    (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x=v)).card=D)
    (hirr : ∀ t : Finset σ, (∀ x∈t, ∀ y∈t, P.cluster x=P.cluster y → x=y) → IsIrred m P.F0 t)
    (E : Finset (Finset R)) (hk : ∀ A∈E, A.card=k) (hA : ∀ A∈E, Avoiding P.graph s A) :
    E.card*D^k ≤ expRank P m s k := by
  let I := (Σ A : E, Choice P.cluster A.1)
  let f (z : I) : Finset σ := selected P.cluster z.1.1 z.2
  let T : Finset (Finset σ) := Finset.univ.image f
  have hcount : T.card=E.card*D^k := by
    rw [Finset.card_image_of_injective _ (sigma_selected_injective P.cluster E),Finset.card_univ]
    change Fintype.card (Σ A : E, Choice P.cluster A.1)=E.card*D^k
    rw [Fintype.card_sigma]
    have he (A : E) : Fintype.card (Choice P.cluster A.1)=D^k := by
      rw [choice_card P.cluster D hcl,hk A.1 A.2]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul]
  rw [←hcount]
  apply P2MExpansionFixedMonomialRank.count P m s k T
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    exact hirr _ (one_per_cluster P.cluster z.1.1 z.2)
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    change (selected P.cluster z.1.1 z.2).card ≤ k
    rw [selected_card,hk z.1.1 z.1.2]
  · intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    change supS P.graph s ((selected P.cluster z.1.1 z.2).image P.cluster)=∅
    rw [selected_image]
    exact sup_eq_empty P.graph s z.1.1 (hA z.1.1 z.1.2)

end SemAC02.Supplement.P2MExpansionAvoidingRank
end

section
-- Inlined Solutions.P2MSamplingJointProbabilities

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MSamplingJointProbabilities

theorem choose_power_compare (N j k : ℕ) (hj : j ≤ N) :
    j.choose k*N^k ≤ N.choose k*j^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k+1 ≤ j
    · have hratio : (j-k)*N ≤ (N-k)*j := by
        rw [Nat.sub_mul,Nat.sub_mul,Nat.mul_comm N j]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hj) _
      apply Nat.le_of_mul_le_mul_right (c:=k+1) ?_ (by omega)
      calc
        _ = (j.choose (k+1)*(k+1))*N^k*N := by rw [pow_succ]; ring
        _ = (j.choose k*(j-k))*N^k*N := by rw [Nat.choose_succ_right_eq]
        _ = (j.choose k*N^k)*((j-k)*N) := by ring
        _ ≤ (N.choose k*j^k)*((j-k)*N) := Nat.mul_le_mul_right _ ih
        _ ≤ (N.choose k*j^k)*((N-k)*j) := Nat.mul_le_mul_left _ hratio
        _ = (N.choose k*(N-k))*j^k*j := by ring
        _ = (N.choose (k+1)*(k+1))*j^k*j := by rw [Nat.choose_succ_right_eq]
        _ = (N.choose (k+1)*j^(k+1))*(k+1) := by rw [pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < k+1)]
      simp

theorem choose_ratio_le (N j k : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    (j.choose k : ℝ)/(N.choose k : ℝ) ≤ ((j : ℝ)/(N : ℝ))^k := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  rw [div_pow]
  apply (div_le_div_iff₀ hC (pow_pos hNp k)).mpr
  have h := choose_power_compare N j k hj
  have hh : (j.choose k : ℝ)*(N : ℝ)^k ≤ (N.choose k : ℝ)*(j : ℝ)^k := by exact_mod_cast h
  nlinarith

theorem joint_bound (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (A : Finset (Fin N)) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·)).card : ℝ)/
      (N.choose j : ℝ) ≤ ((j : ℝ)/(N : ℝ))^A.card := by
  classical
  have hAN : A.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
  by_cases hAj : A.card ≤ j
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ j (Finset.subset_univ _) hAj,
      Finset.card_univ,Fintype.card_fin]
    have hCNj : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
    have hCNk : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (j-A.card) : ℝ)/(N.choose j : ℝ) =
        (j.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNj.ne' hCNk.ne').mpr
      have h := Nat.choose_mul (n:=N) hAj
      have hh : (N.choose j : ℝ)*(j.choose A.card : ℝ) =
          (N.choose A.card : ℝ)*((N-A.card).choose (j-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N j A.card hN hj hAN
  · have he : ((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·) = ∅ := by
      apply Finset.ext
      intro S
      constructor
      · intro hS
        exfalso
        obtain ⟨hSj,hAS⟩ := Finset.mem_filter.mp hS
        have hcard := (Finset.mem_powersetCard.mp hSj).2
        have hh := Finset.card_le_card hAS
        omega
      · simp
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

end AC02Frege.P2MSamplingJointProbabilities
end

section
-- Inlined Solutions.P2MUniformSubsetContainment

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MUniformSubsetContainment

open AC02Frege.P2MSamplingJointProbabilities

theorem probability {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hN : 1 ≤ Fintype.card V) (hk : k ≤ Fintype.card V) (A : Finset V) :
    ((((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)).card : ℝ)/
      ((Fintype.card V).choose k : ℝ) ≤ ((k : ℝ)/(Fintype.card V : ℝ))^A.card := by
  classical
  let N := Fintype.card V
  have hAN : A.card ≤ N := Finset.card_le_univ A
  by_cases hAk : A.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ k (Finset.subset_univ _) hAk,Finset.card_univ]
    have hCNk : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
    have hCNA : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (k-A.card) : ℝ)/(N.choose k : ℝ)=
        (k.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNk.ne' hCNA.ne').mpr
      have h := Nat.choose_mul (n:=N) hAk
      have hh : (N.choose k : ℝ)*(k.choose A.card : ℝ)=
          (N.choose A.card : ℝ)*((N-A.card).choose (k-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N k A.card hN hk hAN
  · have he : ((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSk,hAS⟩ := Finset.mem_filter.mp hS
      have hcard := (Finset.mem_powersetCard.mp hSk).2
      have hh := Finset.card_le_card hAS
      omega
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity


theorem probability_rpow {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) (A : Finset V)
    (b : ℝ) (hb : b ≤ (A.card : ℝ)) :
    ((((Finset.univ : Finset V).powersetCard k).filter (A ⊆ ·)).card : ℝ)/
      ((Fintype.card V).choose k : ℝ) ≤ ((k : ℝ)/(Fintype.card V : ℝ))^b := by
  have hN : 1 ≤ Fintype.card V := hk.trans hkn
  have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hp : (0 : ℝ) < (k : ℝ)/(Fintype.card V : ℝ) :=
    div_pos (by exact_mod_cast (show 0 < k by omega)) hNpos
  have hp1 : (k : ℝ)/(Fintype.card V : ℝ) ≤ 1 :=
    (div_le_one hNpos).mpr (by exact_mod_cast hkn)
  apply (probability k hN hkn A).trans
  rw [←Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hp hp1 hb

end ProofComplexity.P2MUniformSubsetContainment
end

section
-- Inlined Solutions.P2MBoundaryContainmentProbability

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBoundaryContainmentProbability

open PCNonBool

theorem probability {L R : Type} [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (s c : ℝ) (hexp : IsBdryExp G s c)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card R) (J : Finset L) (hJ : (J.card : ℝ) ≤ s) :
    ((((Finset.univ : Finset R).powersetCard k).filter
      (boundaryOn G Finset.univ J ⊆ ·)).card : ℝ)/((Fintype.card R).choose k : ℝ) ≤
      (((k : ℝ)/Fintype.card R)^c)^J.card := by
  have hh := ProofComplexity.P2MUniformSubsetContainment.probability_rpow k hk hkn
    (boundaryOn G Finset.univ J) (c*(J.card : ℝ)) (hexp J hJ)
  have hp : (0 : ℝ) ≤ (k : ℝ)/Fintype.card R := by positivity
  rw [Real.rpow_mul hp,Real.rpow_natCast] at hh
  exact hh

end SemAC02.Supplement.P2MBoundaryContainmentProbability
end

section
-- Inlined Solutions.P2MRootedTreeSetImages

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MRootedTreeSetImages

variable {V : Type} [DecidableEq V]

noncomputable def images (N : V → Finset V) : ℕ → V → Finset (Finset V)
  | 0, u => {{u}}
  | n+1, u => (Finset.HasAntidiagonal.antidiagonal n).attach.biUnion (fun ij =>
      (N u).biUnion (fun v => Finset.image₂ (· ∪ ·) (images N ij.1.1 v) (images N ij.1.2 u)))
termination_by n _ => n
decreasing_by
  all_goals have h := Finset.HasAntidiagonal.mem_antidiagonal.mp ij.2; omega

theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4^n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

theorem cardinal_bound (N : V → Finset V) (Δ : ℕ) (hN : ∀ u, (N u).card ≤ Δ) (n : ℕ) (u : V) :
    (images N n u).card ≤ catalan n*Δ^n := by
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    cases n with
    | zero => simp [images]
    | succ n =>
      have hpair (ij : ↥(Finset.HasAntidiagonal.antidiagonal n)) :
          ((N u).biUnion (fun v => Finset.image₂ (· ∪ ·) (images N ij.1.1 v) (images N ij.1.2 u))).card ≤
            catalan ij.1.1*catalan ij.1.2*Δ^(n+1) := by
        have he : ij.1.1+ij.1.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp ij.2
        calc
          _ ≤ ∑ v∈N u, (Finset.image₂ (· ∪ ·) (images N ij.1.1 v) (images N ij.1.2 u)).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ v∈N u, (images N ij.1.1 v).card*(images N ij.1.2 u).card := by
            apply Finset.sum_le_sum
            intro v hv
            exact Finset.card_image₂_le _ _ _
          _ ≤ ∑ _v∈N u, (catalan ij.1.1*Δ^ij.1.1)*(catalan ij.1.2*Δ^ij.1.2) := by
            apply Finset.sum_le_sum
            intro v hv
            exact Nat.mul_le_mul (ih ij.1.1 (by omega) v) (ih ij.1.2 (by omega) u)
          _ = (N u).card*((catalan ij.1.1*Δ^ij.1.1)*(catalan ij.1.2*Δ^ij.1.2)) := by simp
          _ ≤ Δ*((catalan ij.1.1*Δ^ij.1.1)*(catalan ij.1.2*Δ^ij.1.2)) := Nat.mul_le_mul_right _ (hN u)
          _ = _ := by
            have hp : Δ^ij.1.1*Δ^ij.1.2=Δ^n :=
              (pow_add Δ ij.1.1 ij.1.2).symm.trans (congrArg (fun z => Δ^z) he)
            calc
              _ = catalan ij.1.1*catalan ij.1.2*((Δ^ij.1.1*Δ^ij.1.2)*Δ) := by ring
              _ = _ := by rw [hp,pow_succ]
      rw [images]
      calc
        _ ≤ ∑ ij∈(Finset.HasAntidiagonal.antidiagonal n).attach,
            ((N u).biUnion (fun v => Finset.image₂ (· ∪ ·) (images N ij.1.1 v) (images N ij.1.2 u))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ ij∈(Finset.HasAntidiagonal.antidiagonal n).attach, catalan ij.1.1*catalan ij.1.2*Δ^(n+1) :=
          Finset.sum_le_sum (fun ij hij => hpair ij)
        _ = (∑ ij∈(Finset.HasAntidiagonal.antidiagonal n).attach, catalan ij.1.1*catalan ij.1.2)*Δ^(n+1) := by
          rw [Finset.sum_mul]
        _ = catalan (n+1)*Δ^(n+1) := by
          rw [Finset.sum_attach (f:=fun ij : ℕ×ℕ => catalan ij.1*catalan ij.2),catalan_succ']

theorem exponential_bound (N : V → Finset V) (Δ : ℕ) (hN : ∀ u, (N u).card ≤ Δ) (n : ℕ) (u : V) :
    (images N n u).card ≤ (4*Δ)^n := by
  exact (cardinal_bound N Δ hN n u).trans (by rw [mul_pow]; exact Nat.mul_le_mul_right _ (catalan_le_four_pow n))

end ProofComplexity.P2MRootedTreeSetImages
end

section
-- Inlined Solutions.P2MFiniteSetConnectivity

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MFiniteSetConnectivity

variable {V : Type} [DecidableEq V]

def Symmetric (N : V → Finset V) : Prop := ∀ ⦃u v⦄, v∈N u → u∈N v

def Connected (N : V → Finset V) (S : Finset V) : Prop :=
  ∀ A : Finset V, A⊆S → A.Nonempty → (S\A).Nonempty → ∃ a∈A, ∃ b∈S\A, b∈N a

def ClosedWithin (N : V → Finset V) (S T : Finset V) : Prop :=
  T⊆S ∧ ∀ u∈T, ∀ v∈S, v∈N u → v∈T

theorem exists_component (N : V → Finset V) (S : Finset V) (hS : S.Nonempty) :
    ∃ T : Finset V, T.Nonempty ∧ ClosedWithin N S T ∧ Connected N T := by
  classical
  let E := S.powerset.filter (fun T => T.Nonempty ∧ ClosedWithin N S T)
  have hSmem : S∈E := Finset.mem_filter.mpr ⟨Finset.mem_powerset_self S,hS,Finset.Subset.rfl,
    by intro u hu v hv h; exact hv⟩
  obtain ⟨T,hT,hmin⟩ := E.exists_min_image Finset.card ⟨S,hSmem⟩
  have hprop := (Finset.mem_filter.mp hT).2
  refine ⟨T,hprop.1,hprop.2,?_⟩
  intro A hAT hA hcomp
  by_contra hn
  have hclosed : ClosedWithin N S A := by
    refine ⟨hAT.trans hprop.2.1,?_⟩
    intro u hu v hv hvu
    have hvT : v∈T := hprop.2.2 u (hAT hu) v hv hvu
    by_contra hvA
    exact hn ⟨u,hu,v,Finset.mem_sdiff.mpr ⟨hvT,hvA⟩,hvu⟩
  have hAmem : A∈E := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hclosed.1,hA,hclosed⟩
  have hle := hmin A hAmem
  have hlt : A.card < T.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAT,by
    intro he
    rw [he,Finset.sdiff_self] at hcomp
    exact Finset.not_nonempty_empty hcomp⟩)
  omega

theorem connected_of_root_cuts (N : V → Finset V) (hsym : Symmetric N) (S : Finset V)
    (u : V) (hu : u∈S)
    (hcuts : ∀ A : Finset V, A⊆S → A.Nonempty → u∉A → ∃ a∈A, ∃ b∈S\A, b∈N a) :
    Connected N S := by
  classical
  intro A hA hne hco
  by_cases huA : u∈A
  · obtain ⟨b,hb,a,ha,hab⟩ := hcuts (S\A) Finset.sdiff_subset hco (by simp [huA])
    have haS := (Finset.mem_sdiff.mp ha).1
    have haA : a∈A := by
      by_contra hna
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mpr ⟨haS,hna⟩)
    exact ⟨a,haA,b,hb,hsym hab⟩
  · exact hcuts A hA hne huA

end ProofComplexity.P2MFiniteSetConnectivity
end

section
-- Inlined Solutions.P2MConnectedSetSplitting

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MConnectedSetSplitting

open P2MFiniteSetConnectivity

variable {V : Type} [DecidableEq V]

theorem split (N : V → Finset V) (hsym : Symmetric N) (S : Finset V) (hS : Connected N S)
    (u : V) (hu : u∈S) (hcard : 2 ≤ S.card) :
    ∃ (T B : Finset V) (v : V), v∈T ∧ u∈B ∧ v∈N u ∧ Connected N T ∧ Connected N B ∧
      Disjoint T B ∧ T∪B=S ∧ T.card < S.card ∧ B.card < S.card := by
  classical
  have hrem : (S.erase u).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨T,hT,hclosed,hTconn⟩ := exists_component N (S.erase u) hrem
  have hTS : T⊆S := hclosed.1.trans (Finset.erase_subset _ _)
  have huT : u∉T := fun hh => Finset.notMem_erase u S (hclosed.1 hh)
  let B := S\T
  have huB : u∈B := Finset.mem_sdiff.mpr ⟨hu,huT⟩
  obtain ⟨v,hv,b,hb,hbv⟩ := hS T hTS hT ⟨u,huB⟩
  have hbu : b=u := by
    by_contra hne
    have hbT := hclosed.2 v hv b (Finset.mem_erase.mpr ⟨hne,(Finset.mem_sdiff.mp hb).1⟩) hbv
    exact (Finset.mem_sdiff.mp hb).2 hbT
  have hvu : v∈N u := by subst b; exact hsym hbv
  have hBconn : Connected N B := by
    apply connected_of_root_cuts N hsym B u huB
    intro A hAB hA huA
    have hAS : A⊆S := hAB.trans Finset.sdiff_subset
    obtain ⟨a,ha,b,hb,hba⟩ := hS A hAS hA ⟨u,Finset.mem_sdiff.mpr ⟨hu,huA⟩⟩
    have hbT : b∉T := by
      intro hbT
      have haU : a≠u := by intro he; subst a; exact huA ha
      have haT := hclosed.2 b hbT a (Finset.mem_erase.mpr ⟨haU,hAS ha⟩) (hsym hba)
      exact (Finset.mem_sdiff.mp (hAB ha)).2 haT
    refine ⟨a,ha,b,Finset.mem_sdiff.mpr ⟨?_,(Finset.mem_sdiff.mp hb).2⟩,hba⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1,hbT⟩
  refine ⟨T,B,v,hv,huB,hvu,hTconn,hBconn,(Finset.disjoint_left.mpr (by intro x hx hxB; exact (Finset.mem_sdiff.mp hxB).2 hx)),?_,?_,?_⟩
  · exact Finset.union_sdiff_of_subset hTS
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hTS,?_⟩
    intro he
    exact huT (he ▸ hu)
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    intro he
    have hvB : v∈B := he ▸ hTS hv
    exact (Finset.mem_sdiff.mp hvB).2 hv

end ProofComplexity.P2MConnectedSetSplitting
end

section
-- Inlined Solutions.P2MConnectedSetTreeEncoding

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MConnectedSetTreeEncoding

open P2MFiniteSetConnectivity P2MRootedTreeSetImages Classical

variable {V : Type} [DecidableEq V]

lemma join_mem (N : V → Finset V) (n i j : ℕ) (hij : i+j=n)
    (u v : V) (hvu : v∈N u) (T B : Finset V)
    (hT : T∈images N i v) (hB : B∈images N j u) : T∪B∈images N (n+1) u := by
  rw [images]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨(i,j),Finset.HasAntidiagonal.mem_antidiagonal.mpr hij⟩,Finset.mem_attach _ _,?_⟩
  exact Finset.mem_biUnion.mpr ⟨v,hvu,Finset.mem_image₂.mpr ⟨T,hT,B,hB,rfl⟩⟩

theorem encoded (N : V → Finset V) (hsym : Symmetric N) (j : ℕ)
    (S : Finset V) (hsize : S.card=j) (u : V) (hu : u∈S) (hconn : Connected N S) :
    S∈images N (j-1) u := by
  classical
  induction j using Nat.strong_induction_on generalizing S u with
  | h j ih =>
    have hj : 1 ≤ j := by have hh := Finset.card_pos.mpr ⟨u,hu⟩; omega
    by_cases h1 : S.card=1
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h1
      subst S
      have he : u=v := Finset.mem_singleton.mp hu
      subst u
      have hj' : j=1 := by simpa using hsize.symm
      subst j
      simp [images]
    · have h2 : 2 ≤ S.card := by omega
      obtain ⟨T,B,v,hv,huB,hvu,hTc,hBc,hdis,hunion,hTlt,hBlt⟩ :=
        P2MConnectedSetSplitting.split N hsym S hconn u hu h2
      have hT := ih T.card (by omega) T rfl v hv hTc
      have hB := ih B.card (by omega) B rfl u huB hBc
      have hcards : T.card+B.card=S.card := by rw [←Finset.card_union_of_disjoint hdis,hunion]
      have hTp : 0 < T.card := Finset.card_pos.mpr ⟨v,hv⟩
      have hBp : 0 < B.card := Finset.card_pos.mpr ⟨u,huB⟩
      have he : T.card-1+(B.card-1)=j-2 := by omega
      have hn : j-1=(j-2)+1 := by omega
      rw [hn,←hunion]
      exact join_mem N (j-2) (T.card-1) (B.card-1) he u v hvu T B hT hB

theorem count [Fintype V] (N : V → Finset V) (hsym : Symmetric N) (Δ : ℕ)
    (hN : ∀ u, (N u).card ≤ Δ) (j : ℕ) (hj : 1 ≤ j) :
    ((Finset.univ : Finset (Finset V)).filter (fun S : Finset V => S.card=j ∧ Connected N S)).card ≤
      Fintype.card V*(4*Δ)^(j-1) := by
  classical
  let C := (Finset.univ : Finset (Finset V)).filter (fun S : Finset V => S.card=j ∧ Connected N S)
  have hsub : C⊆Finset.univ.biUnion (images N (j-1)) := by
    intro S hS
    obtain ⟨hsize,hconn⟩ := (Finset.mem_filter.mp hS).2
    have hpos : 0 < S.card := by omega
    obtain ⟨u,hu⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,encoded N hsym j S hsize u hu hconn⟩
  calc
    _ ≤ (Finset.univ.biUnion (images N (j-1))).card := Finset.card_le_card hsub
    _ ≤ ∑ u, (images N (j-1) u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u : V, (4*Δ)^(j-1) := Finset.sum_le_sum (fun u hu => exponential_bound N Δ hN (j-1) u)
    _ = _ := by simp


theorem count_real [Fintype V] (N : V → Finset V) (hsym : Symmetric N) (κ : ℝ) (hκ : 0 ≤ κ)
    (hN : ∀ u, ((N u).card : ℝ) ≤ κ) (j : ℕ) (hj : 1 ≤ j) :
    (((Finset.univ : Finset (Finset V)).filter (fun S : Finset V => S.card=j ∧ Connected N S)).card : ℝ) ≤
      (Fintype.card V : ℝ)*(4*κ)^(j-1) := by
  classical
  have hdeg : ∀ u, (N u).card ≤ Nat.floor κ := fun u => Nat.le_floor (hN u)
  have hc := count N hsym (Nat.floor κ) hdeg j hj
  have hcR : (((Finset.univ : Finset (Finset V)).filter
      (fun S : Finset V => S.card=j ∧ Connected N S)).card : ℝ) ≤
      (Fintype.card V : ℝ)*(4*(Nat.floor κ : ℝ))^(j-1) := by exact_mod_cast hc
  apply hcR.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hκ) (by norm_num)

end ProofComplexity.P2MConnectedSetTreeEncoding
end

section
-- Inlined Solutions.P2MBipartiteConnectedComponents

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MBipartiteConnectedComponents

open PCNonBool P2MFiniteSetConnectivity Classical

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def neighbors (G : BipGraph L R) (u : L) : Finset L :=
  Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, G.Adj u v ∧ G.Adj u' v)

theorem symmetric (G : BipGraph L R) : Symmetric (neighbors G) := by
  intro u u' h
  obtain ⟨hne,v,hu,hu'⟩ := (Finset.mem_filter.mp h).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne.symm,v,hu',hu⟩

theorem boundary_subset (G : BipGraph L R) (J T : Finset L)
    (hT : ClosedWithin (neighbors G) J T) : boundaryOn G Finset.univ T⊆boundaryOn G Finset.univ J := by
  intro v hv
  have hc := (Finset.mem_filter.mp hv).2
  obtain ⟨u,he⟩ := Finset.card_eq_one.mp hc
  have hu : u∈T.filter (fun u' => G.Adj u' v) := by rw [he]; simp
  obtain ⟨huT,huv⟩ := Finset.mem_filter.mp hu
  have heJ : J.filter (fun u' => G.Adj u' v)={u} := by
    ext u'
    constructor
    · intro hu'
      obtain ⟨hu'J,hu'v⟩ := Finset.mem_filter.mp hu'
      by_cases hne : u'=u
      · exact Finset.mem_singleton.mpr hne
      · have hneighbor : u'∈neighbors G u := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hne,v,huv,hu'v⟩
        have hu'T := hT.2 u huT u' hu'J hneighbor
        have hm : u'∈T.filter (fun a => G.Adj a v) := Finset.mem_filter.mpr ⟨hu'T,hu'v⟩
        rwa [he] at hm
    · intro hu'
      have hEq : u'=u := Finset.mem_singleton.mp hu'
      subst u'
      exact Finset.mem_filter.mpr ⟨hT.1 huT,huv⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [heJ,Finset.card_singleton]

theorem connected_witness (G : BipGraph L R) (J : Finset L) (hJ : J.Nonempty) :
    ∃ T : Finset L, T.Nonempty ∧ T⊆J ∧ Connected (neighbors G) T ∧
      boundaryOn G Finset.univ T⊆boundaryOn G Finset.univ J := by
  obtain ⟨T,hT,hclosed,hconn⟩ := exists_component (neighbors G) J hJ
  exact ⟨T,hT,hclosed.1,hconn,boundary_subset G J T hclosed⟩

end ProofComplexity.P2MBipartiteConnectedComponents
end

section
-- Inlined Solutions.P2MBoundaryAvoidanceCount

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MBoundaryAvoidanceCount

open PCNonBool P2MBoundaryAvoidance ProofComplexity ProofComplexity.P2MFiniteSetConnectivity Classical

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def connectedFamily (G : BipGraph L R) (s : ℝ) (j : ℕ) : Finset (Finset L) :=
  Finset.univ.filter (fun J : Finset L => J.card=j ∧ (J.card : ℝ) ≤ s ∧
    Connected (P2MBipartiteConnectedComponents.neighbors G) J)

noncomputable def bad (G : BipGraph L R) (s : ℝ) (k : ℕ) : Finset (Finset R) :=
  (Finset.univ.powersetCard k).filter (fun A => ¬ Avoiding G s A)

noncomputable def good (G : BipGraph L R) (s : ℝ) (k : ℕ) : Finset (Finset R) :=
  (Finset.univ.powersetCard k).filter (Avoiding G s)


lemma good_properties (G : BipGraph L R) (s : ℝ) (k : ℕ) (A : Finset R) (hA : A∈good G s k) :
    A.card=k ∧ Avoiding G s A := by
  exact ⟨(Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2,(Finset.mem_filter.mp hA).2⟩

lemma family_card (G : BipGraph L R) (s κ : ℝ) (hκ : 0 ≤ κ)
    (hdeg : ∀ u, ((P2MBipartiteConnectedComponents.neighbors G u).card : ℝ) ≤ κ)
    (j : ℕ) (hj : 1 ≤ j) :
    ((connectedFamily G s j).card : ℝ) ≤ (Fintype.card L : ℝ)*(4*κ)^(j-1) := by
  have hsub : connectedFamily G s j⊆Finset.univ.filter (fun J : Finset L => J.card=j ∧
      Connected (P2MBipartiteConnectedComponents.neighbors G) J) := by
    intro J hJ
    obtain ⟨hc,hs,hconn⟩ := (Finset.mem_filter.mp hJ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hconn⟩
  have hc : ((connectedFamily G s j).card : ℝ) ≤
      ((Finset.univ.filter (fun J : Finset L => J.card=j ∧
        Connected (P2MBipartiteConnectedComponents.neighbors G) J)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (P2MConnectedSetTreeEncoding.count_real _ (P2MBipartiteConnectedComponents.symmetric G) κ hκ hdeg j hj)

lemma bad_subset (G : BipGraph L R) (s : ℝ) (k : ℕ) : bad G s k⊆
    (Finset.range (Fintype.card L)).biUnion (fun j => (connectedFamily G s (j+1)).biUnion
      (fun J => (Finset.univ.powersetCard k).filter (boundaryOn G Finset.univ J ⊆ ·))) := by
  intro A hA
  obtain ⟨hAk,hnot⟩ := Finset.mem_filter.mp hA
  unfold Avoiding at hnot
  push_neg at hnot
  obtain ⟨J,hJ,hJs,hJA⟩ := hnot
  obtain ⟨T,hT,hTJ,hconn,hbdry⟩ := P2MBipartiteConnectedComponents.connected_witness G J hJ
  have htpos := Finset.card_pos.mpr hT
  have htcard := Finset.card_le_univ T
  have hTle : (T.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast Finset.card_le_card hTJ
  have hTs : (T.card : ℝ) ≤ s := hTle.trans hJs
  have he : T.card=(T.card-1)+1 := by omega
  apply Finset.mem_biUnion.mpr
  refine ⟨T.card-1,Finset.mem_range.mpr (by omega),Finset.mem_biUnion.mpr ?_⟩
  refine ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,hTs,hconn⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨hAk,hbdry.trans hJA⟩

lemma geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    (∑ j∈Finset.range M, q^j) ≤ 1/(1-q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
  have he := geom_sum_mul q M
  have hp := pow_nonneg hq0 M
  nlinarith

theorem bad_card_bound (G : BipGraph L R) (s c : ℝ) (hexp : IsBdryExp G s c)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hdeg : ∀ u, ((P2MBipartiteConnectedComponents.neighbors G u).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card R)
    (hsmall : 4*κ*((k : ℝ)/Fintype.card R)^c < 1) :
    ((bad G s k).card : ℝ) ≤ ((Fintype.card R).choose k : ℝ)*
      ((Fintype.card L : ℝ)*((k : ℝ)/Fintype.card R)^c/(1-4*κ*((k : ℝ)/Fintype.card R)^c)) := by
  let a : ℝ := ((k : ℝ)/Fintype.card R)^c
  let den : ℝ := ((Fintype.card R).choose k : ℝ)
  have hden : 0 < den := by dsimp [den]; exact_mod_cast Nat.choose_pos hkn
  have ha : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have hκ0 : 0 ≤ κ := by linarith
  have hEvent (j : ℕ) (J : Finset L) (hJ : J∈connectedFamily G s (j+1)) :
      (((Finset.univ.powersetCard k).filter (boundaryOn G Finset.univ J ⊆ ·)).card : ℝ) ≤ den*a^(j+1) := by
    have hh := (Finset.mem_filter.mp hJ).2
    have hp := P2MBoundaryContainmentProbability.probability G s c hexp k hk hkn J hh.2.1
    rw [hh.1] at hp
    have he := (div_le_iff₀ hden).mp hp
    simpa only [a,den,mul_comm] using he
  have hfirst : ((bad G s k).card : ℝ) ≤
      ∑ j∈Finset.range (Fintype.card L), ∑ J∈connectedFamily G s (j+1),
        (((Finset.univ.powersetCard k).filter (boundaryOn G Finset.univ J ⊆ ·)).card : ℝ) := by
    have hcard := (Finset.card_le_card (bad_subset G s k)).trans (Finset.card_biUnion_le)
    have hcard' := hcard.trans (Finset.sum_le_sum (fun j hj => Finset.card_biUnion_le))
    exact_mod_cast hcard'
  calc
    _ ≤ ∑ j∈Finset.range (Fintype.card L), ∑ J∈connectedFamily G s (j+1), den*a^(j+1) :=
      hfirst.trans (Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun J hJ => hEvent j J hJ)))
    _ = ∑ j∈Finset.range (Fintype.card L), ((connectedFamily G s (j+1)).card : ℝ)*(den*a^(j+1)) := by simp
    _ ≤ ∑ j∈Finset.range (Fintype.card L), ((Fintype.card L : ℝ)*(4*κ)^j)*(den*a^(j+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Nat.add_sub_cancel] using family_card G s κ hκ0 hdeg (j+1) (by omega)
    _ = den*(Fintype.card L : ℝ)*a*(∑ j∈Finset.range (Fintype.card L), (4*κ*a)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ,mul_pow,mul_pow]
      ring
    _ ≤ den*(Fintype.card L : ℝ)*a*(1/(1-4*κ*a)) :=
      mul_le_mul_of_nonneg_left (geometric_bound (4*κ*a) (by positivity) hsmall _ ) (by positivity)
    _ = _ := by dsimp [a,den]; ring


theorem good_card_bound (G : BipGraph L R) (s c : ℝ) (hexp : IsBdryExp G s c)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hdeg : ∀ u, ((P2MBipartiteConnectedComponents.neighbors G u).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card R)
    (hsmall : 4*κ*((k : ℝ)/Fintype.card R)^c < 1) :
    (1-(Fintype.card L : ℝ)*((k : ℝ)/Fintype.card R)^c/
      (1-4*κ*((k : ℝ)/Fintype.card R)^c))*((Fintype.card R).choose k : ℝ) ≤
        ((good G s k).card : ℝ) := by
  have hpart : (good G s k).card+(bad G s k).card=(Fintype.card R).choose k := by
    rw [good,bad,Finset.card_filter_add_card_filter_not,Finset.card_powersetCard,Finset.card_univ]
  have hpartR : ((good G s k).card : ℝ)+((bad G s k).card : ℝ)=((Fintype.card R).choose k : ℝ) := by
    exact_mod_cast hpart
  have hb := bad_card_bound G s c hexp κ hκ hdeg k hk hkn hsmall
  nlinarith

end SemAC02.Supplement.P2MBoundaryAvoidanceCount
end

section
-- Inlined Solutions.P2MBipartiteIntersectionDegree

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MBipartiteIntersectionDegree

open PCNonBool Classical

theorem bound {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (G : BipGraph L R) (ΔL ΔR : ℕ)
    (hL : ∀ u, (nbrOn G Finset.univ u).card ≤ ΔL)
    (hR : ∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ ΔR) (u : L) :
    (Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, G.Adj u v ∧ G.Adj u' v)).card ≤
      max 1 (ΔL*(ΔR-1)) := by
  let N := nbrOn G Finset.univ u
  let E (v : R) := (Finset.univ.filter (fun u' => G.Adj u' v)).erase u
  have hsub : (Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, G.Adj u v ∧ G.Adj u' v))⊆N.biUnion E := by
    intro u' hu'
    obtain ⟨hne,v,hu,hv⟩ := (Finset.mem_filter.mp hu').2
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,
      Finset.mem_erase.mpr ⟨hne,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩⟩
  have hcard (v : R) (hv : v∈N) : (E v).card ≤ ΔR-1 := by
    have hu : u∈Finset.univ.filter (fun u' => G.Adj u' v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
    dsimp only [E]
    rw [Finset.card_erase_of_mem hu]
    exact Nat.sub_le_sub_right (hR v) 1
  calc
    _ ≤ (N.biUnion E).card := Finset.card_le_card hsub
    _ ≤ ∑ v∈N, (E v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v∈N, (ΔR-1) := Finset.sum_le_sum (fun v hv => hcard v hv)
    _ = N.card*(ΔR-1) := by simp
    _ ≤ ΔL*(ΔR-1) := Nat.mul_le_mul_right _ (hL u)
    _ ≤ _ := Nat.le_max_right _ _

end ProofComplexity.P2MBipartiteIntersectionDegree
end

section
-- Inlined Solutions.P2MExpansionRankBound

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionRankBound

open MvPolynomial ProofComplexity P2MBoundaryAvoidanceCount

theorem rank_bound {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (P : ClusteredRep σ L R) (mo : MonomialOrder σ)
    (s c : ℝ) (hexp : IsBdryExp P.graph s c)
    (D : ℕ) (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x=v)).card=D)
    (hirr : ∀ t : Finset σ, (∀ x∈t, ∀ y∈t, P.cluster x=P.cluster y → x=y) → IsIrred mo P.F0 t)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hκdeg : ∀ u : L, ((Finset.univ.filter (fun u' => u'≠u ∧
      ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card R)
    (hp : 4*κ*((k : ℝ)/Fintype.card R)^c < 1) :
    (1-(Fintype.card L : ℝ)*((k : ℝ)/Fintype.card R)^c/
      (1-4*κ*((k : ℝ)/Fintype.card R)^c))*((Fintype.card R).choose k : ℝ)*(D : ℝ)^k ≤
        (expRank P mo s k : ℝ) := by
  let E := good P.graph s k
  have hdeg : ∀ u, ((P2MBipartiteConnectedComponents.neighbors P.graph u).card : ℝ) ≤ κ := by
    intro u
    exact hκdeg u
  have hcount := good_card_bound P.graph s c hexp κ hκ hdeg k hk hkn hp
  have hEk : ∀ A∈E, A.card=k := by
    intro A hA
    exact (good_properties P.graph s k A hA).1
  have hEA : ∀ A∈E, P2MBoundaryAvoidance.Avoiding P.graph s A := by
    intro A hA
    exact (good_properties P.graph s k A hA).2
  have hrank := P2MExpansionAvoidingRank.count P mo s k D hcl hirr E hEk hEA
  have hrankR : (E.card : ℝ)*(D : ℝ)^k ≤ (expRank P mo s k : ℝ) := by exact_mod_cast hrank
  exact (mul_le_mul_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ (D : ℝ)^k)).trans hrankR

theorem full {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R]
    (P : ClusteredRep σ L R) (mo : MonomialOrder σ) (hmo : IsDegCompatible mo)
    (hml : ∀ f∈P.axioms, AC02Frege.IsMultilinear f)
    (hzero : ∃ y : σ → Bool, ∀ g∈P.F0, eval (toF2 y) g=0) (hresp : P.IsRespectful)
    (s c : ℝ) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hKdeg : ∀ f∈P.axioms, f.totalDegree ≤ K) (hKs : (K : ℝ) ≤ c*s/2-1)
    (D : ℕ) (hD : 0 < D) (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x=v)).card=D)
    (hirr : ∀ t : Finset σ, (∀ x∈t, ∀ y∈t, P.cluster x=P.cluster y → x=y) → IsIrred mo P.F0 t)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hκdeg : ∀ u : L, ((Finset.univ.filter (fun u' => u'≠u ∧
      ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (hkn : k ≤ Fintype.card R)
    (hp : 4*κ*((k : ℝ)/Fintype.card R)^c < 1) :
    (1-(Fintype.card L : ℝ)*((k : ℝ)/Fintype.card R)^c/
      (1-4*κ*((k : ℝ)/Fintype.card R)^c))*((Fintype.card R).choose k : ℝ)*(D : ℝ)^k ≤
        (expRank P mo s k : ℝ) ∧
    ∀ ΔL ΔR : ℕ, (∀ u, (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ ΔL) →
      (∀ v, (Finset.univ.filter (fun u => P.graph.Adj u v)).card ≤ ΔR) →
      ∀ u : L, (Finset.univ.filter (fun u' => u'≠u ∧
        ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card ≤ max 1 (ΔL*(ΔR-1)) := by
  refine ⟨rank_bound P mo s c hexp D hcl hirr κ hκ hκdeg k hk hkn hp,?_⟩
  intro ΔL ΔR hL hR u
  exact P2MBipartiteIntersectionDegree.bound P.graph ΔL ΔR hL hR u

end SemAC02.Supplement.P2MExpansionRankBound
end

end P2MExpansionRankProof
open SemAC02.Supplement MvPolynomial

theorem solution {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L]
    [DecidableEq L] [Fintype R] [DecidableEq R]
    (P : ClusteredRep σ L R) (mo : MonomialOrder σ) (hmo : IsDegCompatible mo)
    (hml : ∀ f ∈ P.axioms, AC02Frege.IsMultilinear f)
    (hzero : ∃ y : σ → Bool, ∀ g ∈ P.F0, eval (toF2 y) g = 0)
    (hresp : P.IsRespectful)
    (s c : ℝ) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hKdeg : ∀ f ∈ P.axioms, f.totalDegree ≤ K) (hKs : (K : ℝ) ≤ c * s / 2 - 1)
    (D : ℕ) (hD : 0 < D) (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x = v)).card = D)
    (hirr : ∀ t : Finset σ, (∀ x ∈ t, ∀ y ∈ t, P.cluster x = P.cluster y → x = y) →
      IsIrred mo P.F0 t)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hκdeg : ∀ u : L, ((Finset.univ.filter (fun u' => u' ≠ u ∧
      ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (hkn : k ≤ Fintype.card R)
    (hp : 4 * κ * ((k : ℝ) / Fintype.card R) ^ c < 1) :
    (1 - (Fintype.card L : ℝ) * ((k : ℝ) / Fintype.card R) ^ c /
        (1 - 4 * κ * ((k : ℝ) / Fintype.card R) ^ c)) *
        ((Fintype.card R).choose k : ℝ) * (D : ℝ) ^ k ≤ (expRank P mo s k : ℝ) ∧
    ∀ ΔL ΔR : ℕ, (∀ u, (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ ΔL) →
      (∀ v, (Finset.univ.filter (fun u => P.graph.Adj u v)).card ≤ ΔR) →
      ∀ u : L, (Finset.univ.filter (fun u' => u' ≠ u ∧
        ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card ≤ max 1 (ΔL * (ΔR - 1))  := by
  exact P2MExpansionRankProof.SemAC02.Supplement.P2MExpansionRankBound.full P mo hmo hml hzero hresp s c hexp K hKdeg hKs D hD hcl hirr κ hκ hκdeg k hk hkK hkn hp
