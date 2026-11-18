-- Prove2me | solution 1 for SemAC02.corollary_4_18_frege_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T19:31:44.968208+00:00
-- url     : https://prove2.me/submissions/84f3a843-1dea-45d0-a9ce-c14a6475b967

import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Mathlib
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_nDivision
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Combinatorics.SetFamily.LYM
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_lift
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_SemAC02_IsRelPseudoRed

section
-- Inlined Solutions.BooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.BooleanAlgebra

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

end AC02Frege.BooleanAlgebra
end

section
-- Inlined Solutions.MajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityFoundation

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

end AC02Frege.MajorityFoundation
end

section
-- Inlined Solutions.BooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation

namespace AC02Frege.BooleanBasis

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

end AC02Frege.BooleanBasis
end

section
-- Inlined Solutions.BooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis

namespace SemAC02.BooleanLocality

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

end SemAC02.BooleanLocality
end

section
-- Inlined Solutions.BooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.BooleanBasis

namespace AC02Frege.BooleanFlip

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

end AC02Frege.BooleanFlip
end

section
-- Inlined Solutions.BooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip

namespace AC02Frege.BooleanRestrictions

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
    (BooleanFlip.flip p).vars ⊆ p.vars := by
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
  toFun := BooleanFlip.flip
  map_add' p q := by simp only [BooleanFlip.flip, map_add]
  map_smul' c p := by simp only [BooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    BooleanFlip.flip p ∈ monomialSpan P := by
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

end AC02Frege.BooleanRestrictions
end

section
-- Inlined Solutions.CommonBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.BooleanRestrictions

namespace SemAC02.CommonBasis

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
    eval (toF2 X) (BooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
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
  have hf : BooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (BooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (BooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = BooleanFlip.flip (BooleanFlip.flip p) := (flip_involution p hml).symm
    _ = BooleanFlip.flip 0 := congrArg (BooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [BooleanFlip.flip]

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

end SemAC02.CommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.CommonBasis


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

namespace ProofComplexity

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

end ProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.FibreBasis

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
  ((ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
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
  change ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [ProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.FibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis

namespace SemAC02.FibreCoordinates

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

end SemAC02.FibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.ProductCoordinates

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
  change (ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact ProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
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

end SemAC02.ProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.CoordinateSpaces

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

end SemAC02.CoordinateSpaces
end

section
-- Inlined Solutions.BooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.MajorityFoundation.eq_zero_or_one (x v)
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
  obtain ⟨r, _, hr⟩ := BooleanLocality.represents_local_function Finset.univ u
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
    (hu : u ∈ SemAC02.CoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.CoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.BooleanFunctionPolynomials
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.Support

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

end AC02Frege.Support
end

section
-- Inlined Solutions.BooleanPC

open MvPolynomial AC02Frege
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanPC

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

end SemAC02.BooleanPC
end

section
-- Inlined Solutions.RelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

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

end SemAC02.RelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

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

end SemAC02.RelativePC
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.ProductCoordinates SemAC02.CoordinateSpaces SemAC02.BooleanLocality

namespace SemAC02.MonomialLocality

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

end SemAC02.MonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.CoordinateSpaces SemAC02.MonomialLocality

namespace SemAC02.CoefficientControl

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

end SemAC02.CoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open SemAC02.FibreBasis SemAC02.FibreCoordinates SemAC02.CoordinateSpaces
open SemAC02.BooleanFunctionPolynomials SemAC02.CoefficientControl

namespace SemAC02.CoefficientPolynomials

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

end SemAC02.CoefficientPolynomials
end

section
-- Inlined Solutions.RelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip AC02Frege.BooleanBasis

namespace SemAC02.RelativeSpaceAlgebra

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
    (hp : RelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    RelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply RelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.RelativeSpaceAlgebra
end

section
-- Inlined Solutions.BooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.BooleanDimension

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

end SemAC02.BooleanDimension
end

section
-- Inlined Solutions.SingletonDivision

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open SemAC02.BooleanFunctionPolynomials SemAC02.RelativeSpaceAlgebra

namespace SemAC02.SingletonDivision

def pointEquiv (n : ℕ) : (Fin n → Bool) ≃ nDivOmega n 1 where
  toFun z := ⟨fun v => z v.1, fun _ _ _ _ _ => Subsingleton.elim _ _⟩
  invFun X i := X.1 (i,0)
  left_inv z := rfl
  right_inv X := by
    apply Subtype.ext
    funext v
    exact congrArg X.1 (Prod.ext rfl (Subsingleton.elim _ _))

noncomputable def collapse (n : ℕ) :
    (nDivOmega n 1 → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (LinearMap.pi (fun z => LinearMap.proj (pointEquiv n z)))

@[simp] theorem eval_collapse (n : ℕ) (u : nDivOmega n 1 → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (collapse n u) = u (pointEquiv n z) := eval_polynomial _ _

theorem collapse_multilinear (n : ℕ) (u : nDivOmega n 1 → ZMod 2) :
    IsMultilinear (collapse n u) := polynomial_multilinear _

theorem collapse_injective (n : ℕ) : Function.Injective (collapse n) := by
  intro u v huv
  funext X
  obtain ⟨z,rfl⟩ := (pointEquiv n).surjective X
  exact (eval_collapse n u z).symm.trans ((congrArg (eval (toF2 z)) huv).trans (eval_collapse n v z))

@[simp] theorem restrOmega_apply (n h : ℕ)
    (p : MvPolynomial (Fin n × Fin h) (ZMod 2)) (X : nDivOmega n h) :
    restrOmega n h p X = eval (toF2 X.1) p := by
  simp only [restrOmega, LinearMap.pi_apply]
  rfl

theorem collapse_restriction (n : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    collapse n (restrOmega n 1 p) = ML (rename Prod.fst p) := by
  apply multilinear_ext_bool (collapse_multilinear n _) (ml_multilinear _)
  intro z
  rw [eval_collapse, restrOmega_apply, eval_ml, eval_rename]
  rfl

theorem collapse_mul (n : ℕ) (u v : nDivOmega n 1 → ZMod 2) :
    collapse n (u*v) = ML (collapse n u * collapse n v) := by
  apply multilinear_ext_bool (collapse_multilinear n _) (ml_multilinear _)
  intro z
  simp only [eval_collapse, eval_ml, map_mul, Pi.mul_apply]

theorem map_BleF0 (n k : ℕ) : (BleF0 n 1 k).map (collapse n) = Ble (Fin n) k := by
  apply le_antisymm
  · rintro p ⟨u,⟨q,hq,rfl⟩,rfl⟩
    rw [collapse_restriction]
    apply (mem_Ble_iff k _).mpr
    exact ⟨ml_multilinear _, (ml_totalDegree_le _).trans ((totalDegree_rename_le _ _).trans
      ((mem_restrictTotalDegree _ k q).mp hq))⟩
  · intro p hp
    let q := rename (fun i : Fin n => (i,(0 : Fin 1))) p
    have hq : q ∈ restrictTotalDegree (Fin n × Fin 1) (ZMod 2) k :=
      (mem_restrictTotalDegree _ k q).mpr ((totalDegree_rename_le _ p).trans ((mem_Ble_iff k p).mp hp).2)
    refine ⟨restrOmega n 1 q, ⟨q,hq,rfl⟩, ?_⟩
    rw [collapse_restriction]
    dsimp [q]
    rw [rename_rename]
    change ML (rename id p) = p
    rw [rename_id_apply]
    exact ml_of_multilinear p ((mem_Ble_iff k p).mp hp).1

theorem HF0_one (n k : ℕ) : HF0 n 1 k = Hn n k := by
  rw [← BooleanDimension.finrank_Ble n k, ← map_BleF0 n k]
  exact (Submodule.equivMapOfInjective (collapse n) (collapse_injective n) _).finrank_eq

theorem map_error (n k : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    ((BleF0 n 1 k).map (LinearMap.mulLeft (ZMod 2) (restrOmega n 1 p))).map (collapse n) =
      multSpace (rename Prod.fst p) k := by
  rw [← Submodule.map_comp]
  change (BleF0 n 1 k).map _ = (Ble (Fin n) k).map (mulML (rename Prod.fst p))
  rw [← map_BleF0 n k, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro u
  change collapse n (restrOmega n 1 p * u) = ML (rename Prod.fst p * collapse n u)
  rw [collapse_mul, collapse_restriction, ml_mul_left]

theorem finrank_error (n k : ℕ) (p : MvPolynomial (Fin n × Fin 1) (ZMod 2)) :
    finrank (ZMod 2) ((BleF0 n 1 k).map (LinearMap.mulLeft (ZMod 2) (restrOmega n 1 p))) =
      finrank (ZMod 2) (multSpace (rename Prod.fst p) k) := by
  rw [← map_error n k p]
  exact (Submodule.equivMapOfInjective (collapse n) (collapse_injective n) _).finrank_eq

end SemAC02.SingletonDivision
end

section
-- Inlined Solutions.StandardMonomials

open Module MvPolynomial
open scoped MonomialOrder

namespace ProofComplexity.StandardMonomials

def Standard {σ : Type*} (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (ZMod 2)))
    (s : σ →₀ ℕ) : Prop := ∀ p ∈ I, p ≠ 0 → m.degree p ≠ s

theorem downward {σ : Type*} (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (ZMod 2)))
    {s t : σ →₀ ℕ} (ht : Standard m I t) (hst : s ≤ t) : Standard m I s := by
  classical
  intro p hp hne hdeg
  let q : MvPolynomial σ (ZMod 2) := monomial (t-s) 1
  have hq : q ≠ 0 := by exact mt monomial_eq_zero.mp one_ne_zero
  have hprod : p*q ≠ 0 := mul_ne_zero hne hq
  have hprodI : p*q ∈ I := I.mul_mem_right q hp
  have hlead : m.leadingCoeff p * m.leadingCoeff q ≠ 0 :=
    mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hne) (m.leadingCoeff_ne_zero_iff.mpr hq)
  have hproddeg : m.degree (p*q) = t := by
    rw [m.degree_mul_of_mul_leadingCoeff_ne_zero hlead,hdeg]
    have hqdeg : m.degree q = t-s := by simp [q,m.degree_monomial]
    rw [hqdeg]
    exact add_tsub_cancel_of_le hst
  exact ht (p*q) hprodI hprod hproddeg

noncomputable def supported {σ : Type*} (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) := restrictSupport (ZMod 2) {s | Standard m I s}

theorem supported_disjoint_ideal {σ : Type*} (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) (hp : p ∈ supported m I) (hpI : p ∈ I) : p = 0 := by
  by_contra hne
  have hs : Standard m I (m.degree p) := hp (m.degree_mem_support hne)
  exact hs p hpI hne rfl

theorem image_independent {σ V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ (ZMod 2)))
    (T : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] V) (hker : ∀ p, p ∈ I ↔ T p = 0) :
    LinearIndependent (ZMod 2) (fun s : {s // Standard m I s} => T (monomial s.1 1)) := by
  classical
  let v := fun s : {s // Standard m I s} => (monomial s.1 1 : MvPolynomial σ (ZMod 2))
  have hv : LinearIndependent (ZMod 2) v := (basisMonomials σ (ZMod 2)).linearIndependent.comp
    Subtype.val Subtype.val_injective
  have hspan : Submodule.span (ZMod 2) (Set.range v) ≤ supported m I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact (monomial_mem_restrictSupport (ZMod 2)).mpr (Or.inl s.2)
  apply hv.map_injOn T
  intro p hp q hq he
  apply sub_eq_zero.mp
  apply supported_disjoint_ideal m I (p-q) ((supported m I).sub_mem (hspan hp) (hspan hq))
  exact (hker _).mpr (by simp only [map_sub,he,sub_self])

theorem standard_remainder {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ I ∧ r.totalDegree ≤ p.totalDegree ∧
      ∀ s ∈ r.support, Standard MonomialOrder.degLex I s := by
  classical
  let m : MonomialOrder σ := MonomialOrder.degLex
  let B : Set (MvPolynomial σ (ZMod 2)) := {b | b ∈ I ∧ b ≠ 0}
  obtain ⟨g,r,heq,hdeg,hrem⟩ := m.div_set (B := B)
    (fun b hb => isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hb.2)) p
  let q := Finsupp.linearCombination (MvPolynomial σ (ZMod 2)) (fun b : B => b.1) g
  have hqI : q ∈ I := by
    change Finsupp.linearCombination _ _ g ∈ I
    rw [Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro b _
    exact I.smul_mem (g b) b.2.1
  have hqdeg : q.totalDegree ≤ p.totalDegree := by
    change (Finsupp.linearCombination (MvPolynomial σ (ZMod 2)) (fun b : B => b.1) g).totalDegree ≤ _
    rw [Finsupp.linearCombination_apply]
    apply totalDegree_finsetSum_le
    intro b _
    have hb := MvPolynomial.degLex_totalDegree_monotone (hdeg b)
    simpa only [smul_eq_mul,mul_comm] using hb
  have hr : r = p-q := by
    change p = q+r at heq
    rw [heq]
    ring
  refine ⟨r,?_,?_,?_⟩
  · rw [hr]
    simpa only [sub_sub_cancel] using hqI
  · rw [hr]
    exact (totalDegree_sub _ _).trans (max_le le_rfl hqdeg)
  · intro s hs b hb hne hbs
    exact hrem s hs b ⟨hb,hne⟩ (hbs ▸ le_rfl)

theorem degree_image_span {σ V : Type*} [LinearOrder σ] [WellFoundedGT σ]
    [AddCommGroup V] [Module (ZMod 2) V]
    (I : Ideal (MvPolynomial σ (ZMod 2))) (T : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] V)
    (hker : ∀ p, p ∈ I ↔ T p = 0) (k : ℕ) :
    (restrictTotalDegree σ (ZMod 2) k).map T =
      Submodule.span (ZMod 2) (Set.range (fun s : {s : σ →₀ ℕ //
        Standard MonomialOrder.degLex I s ∧ s.sum (fun _ e => e) ≤ k} => T (monomial s.1 1))) := by
  classical
  apply le_antisymm
  · rintro v ⟨p,hp,rfl⟩
    obtain ⟨r,hrI,hrdeg,hrstd⟩ := standard_remainder I p
    have he : T p = T r := sub_eq_zero.mp (by rw [← map_sub]; exact (hker _).mp hrI)
    rw [he,r.as_sum,map_sum]
    apply Submodule.sum_mem
    intro s hs
    have hdeg : s.sum (fun _ e => e) ≤ k :=
      (le_totalDegree hs).trans (hrdeg.trans ((mem_restrictTotalDegree σ k p).mp hp))
    have hmon : monomial s (r.coeff s) = (r.coeff s) • monomial s (1 : ZMod 2) := by
      simp only [smul_monomial,smul_eq_mul,mul_one]
    rw [hmon,map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨s,hrstd s hs,hdeg⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨s,rfl⟩
    refine ⟨monomial s.1 1,(mem_restrictTotalDegree σ k _).mpr ?_,rfl⟩
    rw [totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
    exact s.2.2

end ProofComplexity.StandardMonomials
end

section
-- Inlined Solutions.DivisionBlockBasis

open Module

namespace SemAC02.DivisionBlockBasis

noncomputable def valueEquiv (h : ℕ) :
    (Option (Fin h) → ZMod 2) ≃ₗ[ZMod 2] (Option (Fin h) → ZMod 2) where
  toFun c x := match x with | none => c none | some j => c none + c (some j)
  invFun c x := match x with | none => c none | some j => c none + c (some j)
  left_inv c := by
    funext x
    cases x with
    | none => rfl
    | some j => simp only [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  right_inv c := by
    funext x
    cases x with
    | none => rfl
    | some j => simp only [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  map_add' c d := by
    funext x
    cases x with
    | none => rfl
    | some j => change (c none+d none)+(c (some j)+d (some j)) = (c none+c (some j))+(d none+d (some j)); ring
  map_smul' a c := by
    funext x
    cases x with
    | none => rfl
    | some j =>
      change a • c none + a • c (some j) = a • (c none+c (some j))
      exact (smul_add a (c none) (c (some j))).symm

noncomputable def blockBasis (h : ℕ) :
    Basis (Option (Fin h)) (ZMod 2) (Option (Fin h) → ZMod 2) :=
  (Pi.basisFun (ZMod 2) (Option (Fin h))).map (valueEquiv h)

@[simp] theorem blockBasis_none (h : ℕ) (x : Option (Fin h)) : blockBasis h none x = 1 := by
  classical
  rw [blockBasis,Basis.map_apply]
  cases x <;> simp [valueEquiv,Pi.basisFun_apply]

@[simp] theorem blockBasis_some (h : ℕ) (j : Fin h) (x : Option (Fin h)) :
    blockBasis h (some j) x = if x = some j then 1 else 0 := by
  classical
  rw [blockBasis,Basis.map_apply]
  cases x with
  | none => simp [valueEquiv,Pi.basisFun_apply]
  | some k => simp [valueEquiv,Pi.basisFun_apply,Pi.single_apply,eq_comm]

end SemAC02.DivisionBlockBasis
end

section
-- Inlined Solutions.DivisionPoints

namespace SemAC02.DivisionPoints

noncomputable def encode (n h : ℕ) (S : Fin n → Option (Fin h)) : nDivOmega n h := by
  classical
  refine ⟨fun v => decide (S v.1 = some v.2),?_⟩
  intro i j j' hj hj'
  simp only [decide_eq_true_eq] at hj hj'
  exact Option.some.inj (hj.symm.trans hj')

noncomputable def decode (n h : ℕ) (X : nDivOmega n h) (i : Fin n) : Option (Fin h) := by
  classical
  exact if hx : ∃ j, X.1 (i,j) = true then some (Classical.choose hx) else none

theorem decode_eq_some (n h : ℕ) (X : nDivOmega n h) (i : Fin n) (j : Fin h) :
    decode n h X i = some j ↔ X.1 (i,j) = true := by
  classical
  unfold decode
  split_ifs with hx
  · constructor
    · intro he
      have hj := Option.some.inj he
      rw [← hj]
      exact Classical.choose_spec hx
    · intro hj
      exact congrArg some (X.2 i (Classical.choose hx) j (Classical.choose_spec hx) hj)
  · simp only [Option.noConfusion, false_iff]
    exact fun hj => hx ⟨j,hj⟩

noncomputable def pointEquiv (n h : ℕ) : (Fin n → Option (Fin h)) ≃ nDivOmega n h where
  toFun := encode n h
  invFun := decode n h
  left_inv S := by
    classical
    funext i
    cases hs : S i with
    | none =>
      cases hd : decode n h (encode n h S) i with
      | none => rfl
      | some j =>
        have hb := (decode_eq_some n h (encode n h S) i j).mp hd
        simp [encode,hs] at hb
    | some j =>
      apply (decode_eq_some n h (encode n h S) i j).mpr
      simp [encode,hs]
  right_inv X := by
    classical
    apply Subtype.ext
    funext v
    apply Bool.eq_iff_iff.mpr
    simp only [encode,decide_eq_true_eq,decode_eq_some]

end SemAC02.DivisionPoints
end

section
-- Inlined Solutions.DivisionMonomialBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.DivisionMonomialBasis

noncomputable def divisionBasis (n h : ℕ) :
    Basis (Fin n → Option (Fin h)) (ZMod 2) (nDivOmega n h → ZMod 2) :=
  (ProofComplexity.productFunctionBasis (fun _i : Fin n => DivisionBlockBasis.blockBasis h)).map
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (DivisionPoints.pointEquiv n h).symm)

noncomputable def assemble {n h : ℕ} (S : Fin n → Option (Fin h)) : Finset (Fin n × Fin h) := by
  classical
  exact Finset.univ.filter (fun v => S v.1 = some v.2)

theorem section_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) (i : Fin n) :
    blockSection (assemble S) i = match S i with | none => ∅ | some j => {j} := by
  classical
  ext j
  cases hs : S i <;> simp [blockSection,assemble,hs,eq_comm]

@[simp] theorem divisionBasis_apply (n h : ℕ) (S : Fin n → Option (Fin h)) (X : nDivOmega n h) :
    divisionBasis n h S X = eval (toF2 X.1) (xMon (assemble S)) := by
  classical
  rw [divisionBasis,Basis.map_apply]
  change ProofComplexity.productFunctionBasis (fun _i : Fin n => DivisionBlockBasis.blockBasis h) S
    ((DivisionPoints.pointEquiv n h).symm X) = _
  rw [ProofComplexity.productFunctionBasis_apply,FibreBasis.xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [section_assemble]
  cases hs : S i with
  | none => simp only [DivisionBlockBasis.blockBasis_none,xMon,Finset.prod_empty,map_one]
  | some j =>
    rw [DivisionBlockBasis.blockBasis_some]
    change (if DivisionPoints.decode n h X i = some j then 1 else 0) = _
    simp only [DivisionPoints.decode_eq_some,xMon,Finset.prod_singleton,eval_X,toF2]

noncomputable def active {n h : ℕ} (S : Fin n → Option (Fin h)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (S i).isSome)

theorem image_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (assemble S).image Prod.fst = active S := by
  classical
  ext i
  constructor
  · rintro hi
    obtain ⟨⟨i',j⟩,hj,rfl⟩ := Finset.mem_image.mp hi
    have hs : S i' = some j := by simpa only [assemble,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,hs,Option.isSome_some]
  · intro hi
    have hs : (S i).isSome := by simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    cases hSi : S i with
    | none => simp [hSi] at hs
    | some j => exact Finset.mem_image.mpr ⟨(i,j),by simp [assemble,hSi],rfl⟩

theorem assemble_card {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (assemble S).card = (active S).card := by
  classical
  rw [← image_assemble S]
  apply (Finset.card_image_of_injOn ?_).symm
  rintro ⟨i,j⟩ h1 ⟨i',j'⟩ h2 he
  have hi : i = i' := he
  subst i'
  have hs1 : S i = some j := by simpa [assemble] using h1
  have hs2 : S i = some j' := by simpa [assemble] using h2
  exact Prod.ext rfl (Option.some.inj (hs1.symm.trans hs2))

theorem xMon_degree {n h : ℕ} (S : Fin n → Option (Fin h)) :
    (xMon (assemble S)).totalDegree = (active S).card :=
  (xMon_totalDegree _).trans (assemble_card S)

end SemAC02.DivisionMonomialBasis
end

section
-- Inlined Solutions.DivisionSupports

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.DivisionMonomialBasis

namespace SemAC02.DivisionSupports

def Valid {n h : ℕ} (A : Finset (Fin n × Fin h)) : Prop :=
  ∀ i j j', (i,j) ∈ A → (i,j') ∈ A → j = j'

noncomputable def pointOfSupport {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : nDivOmega n h := by
  classical
  refine ⟨fun v => decide (v ∈ A),?_⟩
  intro i j j' hj hj'
  exact hA i j j' (by simpa only [decide_eq_true_eq] using hj) (by simpa only [decide_eq_true_eq] using hj')

noncomputable def sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : Fin n → Option (Fin h) :=
  DivisionPoints.decode n h (pointOfSupport A hA)

theorem assemble_sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) :
    assemble (sections A hA) = A := by
  classical
  ext v
  simp only [assemble,Finset.mem_filter,Finset.mem_univ,true_and,sections,DivisionPoints.decode_eq_some,
    pointOfSupport,decide_eq_true_eq]

theorem valid_assemble {n h : ℕ} (S : Fin n → Option (Fin h)) : Valid (assemble S) := by
  classical
  intro i j j' hj hj'
  have h1 : S i = some j := by simpa [assemble] using hj
  have h2 : S i = some j' := by simpa [assemble] using hj'
  exact Option.some.inj (h1.symm.trans h2)

theorem xMon_invalid {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : ¬ Valid A) :
    restrOmega n h (xMon A) = 0 := by
  classical
  funext X
  rw [SingletonDivision.restrOmega_apply]
  change eval (toF2 X.1) (xMon A) = 0
  by_contra hn
  rw [xMon_eval] at hn
  have hbit : ∀ v ∈ A, X.1 v = true := by
    intro v hv
    have hne := Finset.prod_ne_zero_iff.mp hn v hv
    cases he : X.1 v <;> simp [toF2,he] at hne ⊢
  exact hA (fun i j j' hj hj' => X.2 i j j' (hbit _ hj) (hbit _ hj'))

theorem monomial_restriction {n h : ℕ} (s : (Fin n × Fin h) →₀ ℕ) (c : ZMod 2) :
    restrOmega n h (monomial s c) = c • restrOmega n h (xMon s.support) := by
  funext X
  simp only [SingletonDivision.restrOmega_apply,Pi.smul_apply,smul_eq_mul]
  exact MonomialLocality.eval_monomial_squarefree s c (toF2 X.1)

end SemAC02.DivisionSupports
end

section
-- Inlined Solutions.DivisionDegreeBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.DivisionMonomialBasis SemAC02.DivisionSupports

namespace SemAC02.DivisionDegreeBasis

abbrev DegreeIndex (n h k : ℕ) := {S : Fin n → Option (Fin h) // (active S).card ≤ k}

noncomputable def degreeSpan (n h k : ℕ) : Submodule (ZMod 2) (nDivOmega n h → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun S : DegreeIndex n h k => divisionBasis n h S.1))

theorem BleF0_eq_span (n h k : ℕ) : BleF0 n h k = degreeSpan n h k := by
  classical
  apply le_antisymm
  · rintro f ⟨p,hp,rfl⟩
    have hpdeg := (mem_restrictTotalDegree _ k p).mp hp
    rw [p.as_sum,map_sum]
    apply Submodule.sum_mem
    intro s hs
    rw [monomial_restriction]
    apply Submodule.smul_mem
    by_cases hvalid : Valid s.support
    · let S := sections s.support hvalid
      have hScard : (active S).card ≤ k := by
        rw [← assemble_card S]
        change (assemble (sections s.support hvalid)).card ≤ k
        rw [assemble_sections]
        exact (MonomialLocality.support_card_le_sum s).trans ((le_totalDegree hs).trans hpdeg)
      have he : restrOmega n h (xMon s.support) = divisionBasis n h S := by
        funext X
        rw [SingletonDivision.restrOmega_apply,divisionBasis_apply]
        rw [show assemble S = s.support from assemble_sections _ _]
      rw [he]
      exact Submodule.subset_span ⟨⟨S,hScard⟩,rfl⟩
    · rw [xMon_invalid _ hvalid]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨S,rfl⟩
    refine ⟨xMon (assemble S.1), (mem_restrictTotalDegree _ k _).mpr ((xMon_degree S.1).trans_le S.2), ?_⟩
    funext X
    exact (divisionBasis_apply n h S.1 X).symm

noncomputable def degreeBasis (n h k : ℕ) :
    Basis (DegreeIndex n h k) (ZMod 2) (BleF0 n h k) :=
  (Basis.span ((divisionBasis n h).linearIndependent.comp (fun S : DegreeIndex n h k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (BleF0_eq_span n h k).symm)

instance finite_BleF0 (n h k : ℕ) : Module.Finite (ZMod 2) (BleF0 n h k) := by
  classical
  exact Module.Finite.of_basis (degreeBasis n h k)

theorem HF0_eq_card (n h k : ℕ) : HF0 n h k = Fintype.card (DegreeIndex n h k) := by
  classical
  exact Module.finrank_eq_card_basis (degreeBasis n h k)

end SemAC02.DivisionDegreeBasis
end

section
-- Inlined Solutions.DivisionStandardIdeal

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis
open scoped MonomialOrder
open ProofComplexity.StandardMonomials

namespace SemAC02.DivisionStandardIdeal

noncomputable def evaluation {n h : ℕ} (a : nDivOmega n h → ZMod 2) :
    MvPolynomial (Fin n × Fin h) (ZMod 2) →ₗ[ZMod 2] (nDivOmega n h → ZMod 2) :=
  (LinearMap.mulLeft (ZMod 2) a).comp (restrOmega n h)

@[simp] theorem evaluation_apply {n h : ℕ} (a : nDivOmega n h → ZMod 2)
    (p : MvPolynomial (Fin n × Fin h) (ZMod 2)) (X : nDivOmega n h) :
    evaluation a p X = a X * eval (toF2 X.1) p := by
  simp only [evaluation,LinearMap.comp_apply,LinearMap.mulLeft_apply,Pi.mul_apply,SingletonDivision.restrOmega_apply]

noncomputable def restrictedEval {n h : ℕ} (a : nDivOmega n h → ZMod 2) :
    MvPolynomial (Fin n × Fin h) (ZMod 2) →+* ({X : nDivOmega n h // a X ≠ 0} → ZMod 2) where
  toFun p X := eval (toF2 X.1.1) p
  map_zero' := by funext X; exact map_zero _
  map_one' := by funext X; exact map_one _
  map_add' p q := by funext X; exact map_add _ p q
  map_mul' p q := by funext X; exact map_mul _ p q

noncomputable def annihilatorIdeal {n h : ℕ} (a : nDivOmega n h → ZMod 2) :
    Ideal (MvPolynomial (Fin n × Fin h) (ZMod 2)) := RingHom.ker (restrictedEval a)

theorem mem_annihilator {n h : ℕ} (a : nDivOmega n h → ZMod 2)
    (p : MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    p ∈ annihilatorIdeal a ↔ evaluation a p = 0 := by
  constructor
  · intro hp
    have he : restrictedEval a p = 0 := hp
    funext X
    rw [evaluation_apply]
    by_cases ha : a X = 0
    · rw [ha,zero_mul]; rfl
    · have hz := congrFun he (⟨X,ha⟩ : {X : nDivOmega n h // a X ≠ 0})
      change eval (toF2 X.1) p = 0 at hz
      rw [hz,mul_zero]; rfl
  · intro hp
    change restrictedEval a p = 0
    funext X
    have hz := congrFun hp X.1
    change a X.1 * eval (toF2 X.1.1) p = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left X.2

theorem squarefree_of_standard {n h : ℕ} (a : nDivOmega n h → ZMod 2)
    (m : MonomialOrder (Fin n × Fin h)) (s : (Fin n × Fin h) →₀ ℕ)
    (hs : Standard m (annihilatorIdeal a) s) : ∀ v, s v ≤ 1 := by
  classical
  by_contra! hbad
  have hsqle : sqfree s ≤ s := by intro v; simp [sqfree,Finsupp.mapRange_apply]
  have hsqne : sqfree s ≠ s := by
    intro he
    obtain ⟨v,hv⟩ := hbad
    have he' := congrArg (fun t => t v) he
    simp only [sqfree,Finsupp.mapRange_apply] at he'
    omega
  let p : MvPolynomial (Fin n × Fin h) (ZMod 2) := monomial s 1 - monomial (sqfree s) 1
  have hpI : p ∈ annihilatorIdeal a := by
    apply (mem_annihilator a p).mpr
    funext X
    simp only [evaluation_apply,p,map_sub,mul_sub]
    have he : eval (toF2 X.1) (monomial (sqfree s) (1 : ZMod 2)) = eval (toF2 X.1) (monomial s 1) := by
      rw [← ml_monomial,eval_ml]
    rw [he,sub_self]
    rfl
  have hlt : m.degree (monomial (sqfree s) (1 : ZMod 2)) ≺[m] m.degree (monomial s (1 : ZMod 2)) := by
    simp only [m.degree_monomial,if_false,one_ne_zero]
    exact m.toSyn_strictMono (lt_of_le_of_ne hsqle hsqne)
  have hpdeg : m.degree p = s := by
    dsimp only [p]
    rw [m.degree_sub_of_lt hlt]
    simp [m.degree_monomial]
  have hpne : p ≠ 0 := by
    intro hp0
    have he := congrArg (MvPolynomial.coeff s) hp0
    simp [p,coeff_monomial,hsqne,Ne.symm hsqne] at he
  exact hs p hpI hpne hpdeg

theorem valid_of_standard {n h : ℕ} (a : nDivOmega n h → ZMod 2)
    (m : MonomialOrder (Fin n × Fin h)) (s : (Fin n × Fin h) →₀ ℕ)
    (hs : Standard m (annihilatorIdeal a) s) : DivisionSupports.Valid s.support := by
  classical
  by_contra hbad
  have hz := DivisionSupports.xMon_invalid s.support hbad
  have hsfree := squarefree_of_standard a m s hs
  have hpI : monomial s (1 : ZMod 2) ∈ annihilatorIdeal a := by
    apply (mem_annihilator a _).mpr
    rw [squarefree_monomial s 1 hsfree,one_smul]
    change a * restrOmega n h (xMon s.support) = 0
    rw [hz,mul_zero]
  exact hs _ hpI (mt monomial_eq_zero.mp (one_ne_zero : (1 : ZMod 2) ≠ 0))
    (by simp [m.degree_monomial])

end SemAC02.DivisionStandardIdeal
end

section
-- Inlined Solutions.DivisionStandardFamily

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis
open ProofComplexity.StandardMonomials
open scoped MonomialOrder

namespace SemAC02.DivisionStandardFamily

local instance variableOrder (n h : ℕ) : LinearOrder (Fin n × Fin h) :=
  LinearOrder.lift' (toLex : (Fin n × Fin h) → Lex (Fin n × Fin h)) (fun _ _ he => he)

local instance variableWellFounded (n h : ℕ) : @WellFoundedGT (Fin n × Fin h) (variableOrder n h).toLT :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

noncomputable def exponent {V : Type*} (A : Finset V) : V →₀ ℕ := by
  classical
  exact Finsupp.indicator A (fun _ _ => 1)

theorem exponent_sum {V : Type*} (A : Finset V) : (exponent A).sum (fun _ e => e) = A.card := by
  have he := congrArg MvPolynomial.totalDegree (xMon_eq_monomial (V := V) A)
  simpa only [exponent,xMon_totalDegree,totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)] using he.symm

theorem exponent_mono {V : Type*} {A B : Finset V} (hAB : A ⊆ B) : exponent A ≤ exponent B := by
  classical
  intro v
  simp only [exponent,Finsupp.indicator_apply]
  split_ifs with hvA hvB
  · exact le_rfl
  · exact False.elim (hvB (hAB hvA))
  · exact Nat.zero_le _
  · exact le_rfl

noncomputable def family {n h : ℕ} (a : nDivOmega n h → ZMod 2) : Finset (Finset (Fin n × Fin h)) := by
  classical
  exact Finset.univ.filter (fun A => DivisionSupports.Valid A ∧
    Standard MonomialOrder.degLex (DivisionStandardIdeal.annihilatorIdeal a) (exponent A))

theorem mem_family {n h : ℕ} (a : nDivOmega n h → ZMod 2) (A : Finset (Fin n × Fin h)) :
    A ∈ family a ↔ DivisionSupports.Valid A ∧
      Standard MonomialOrder.degLex (DivisionStandardIdeal.annihilatorIdeal a) (exponent A) := by
  classical
  simp only [family,Finset.mem_filter,Finset.mem_univ,true_and]

theorem family_downward {n h : ℕ} (a : nDivOmega n h → ZMod 2)
    (A : Finset (Fin n × Fin h)) (hA : A ∈ family a) (B : Finset (Fin n × Fin h)) (hB : B ⊆ A) : B ∈ family a := by
  obtain ⟨hvalid,hstd⟩ := (mem_family a A).mp hA
  apply (mem_family a B).mpr
  refine ⟨fun i j j' hj hj' => hvalid i j j' (hB hj) (hB hj'),?_⟩
  exact downward MonomialOrder.degLex _ hstd (exponent_mono hB)

abbrev Index {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :=
  {A : Finset (Fin n × Fin h) // A ∈ family a ∧ A.card ≤ k}

abbrev StandardIndex {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :=
  {s : (Fin n × Fin h) →₀ ℕ // Standard MonomialOrder.degLex (DivisionStandardIdeal.annihilatorIdeal a) s ∧
    s.sum (fun _ e => e) ≤ k}

noncomputable def indexEquiv {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    StandardIndex a k ≃ Index a k where
  toFun s := ⟨s.1.support,by
    have hsfree := DivisionStandardIdeal.squarefree_of_standard a MonomialOrder.degLex s.1 s.2.1
    have hsEq : s.1 = exponent s.1.support := squarefree_eq_indicator s.1 hsfree
    exact ⟨(mem_family a _).mpr ⟨DivisionStandardIdeal.valid_of_standard a MonomialOrder.degLex s.1 s.2.1,
      hsEq ▸ s.2.1⟩,by rw [← squarefree_sum s.1 hsfree]; exact s.2.2⟩⟩
  invFun A := ⟨exponent A.1,(mem_family a A.1).mp A.2.1 |>.2,by rw [exponent_sum]; exact A.2.2⟩
  left_inv s := by
    apply Subtype.ext
    exact (squarefree_eq_indicator s.1 (DivisionStandardIdeal.squarefree_of_standard a MonomialOrder.degLex s.1 s.2.1)).symm
  right_inv A := by
    apply Subtype.ext
    exact indicator_support A.1

theorem index_monomial {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) (A : Index a k) :
    monomial ((indexEquiv a k).symm A).1 (1 : ZMod 2) = xMon A.1 := (xMon_eq_monomial A.1).symm

theorem degree_image_span {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    (BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) a) =
      Submodule.span (ZMod 2) (Set.range (fun A : Index a k => DivisionStandardIdeal.evaluation a (xMon A.1))) := by
  classical
  unfold BleF0
  rw [← Submodule.map_comp]
  change (restrictTotalDegree _ _ k).map (DivisionStandardIdeal.evaluation a) = _
  rw [ProofComplexity.StandardMonomials.degree_image_span _ _ (DivisionStandardIdeal.mem_annihilator a)]
  congr 1
  ext v
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨indexEquiv a k s,?_⟩
    dsimp only
    rw [← index_monomial a k,Equiv.symm_apply_apply]
  · rintro ⟨A,rfl⟩
    exact ⟨(indexEquiv a k).symm A,congrArg (DivisionStandardIdeal.evaluation a) (index_monomial a k A)⟩

theorem family_independent {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    LinearIndependent (ZMod 2) (fun A : Index a k => DivisionStandardIdeal.evaluation a (xMon A.1)) := by
  have hall := image_independent MonomialOrder.degLex (DivisionStandardIdeal.annihilatorIdeal a)
    (DivisionStandardIdeal.evaluation a) (DivisionStandardIdeal.mem_annihilator a)
  have hbounded := hall.comp (fun s : StandardIndex a k => ⟨s.1,s.2.1⟩) (by
    intro s t he
    apply Subtype.ext
    exact congrArg (fun u : {s : (Fin n × Fin h) →₀ ℕ //
      Standard MonomialOrder.degLex (DivisionStandardIdeal.annihilatorIdeal a) s} => u.1) he)
  have h := hbounded.comp (indexEquiv a k).symm (indexEquiv a k).symm.injective
  simpa only [Function.comp_def,index_monomial] using h

theorem rank_eq_card {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) a)) = Fintype.card (Index a k) := by
  classical
  rw [degree_image_span]
  exact finrank_span_eq_card (family_independent a k)

end SemAC02.DivisionStandardFamily
end

section
-- Inlined Solutions.DivisionDimensionCounts

open Module
open SemAC02.DivisionMonomialBasis

namespace SemAC02.DivisionDimensionCounts

noncomputable def withSupport {n h : ℕ} (I : Finset (Fin n)) (v : I → Fin h) : Fin n → Option (Fin h) := by
  classical
  exact fun i => if hi : i ∈ I then some (v ⟨i,hi⟩) else none

theorem active_withSupport {n h : ℕ} (I : Finset (Fin n)) (v : I → Fin h) : active (withSupport I v) = I := by
  classical
  ext i
  by_cases hi : i ∈ I <;> simp [active,withSupport,hi]

noncomputable def valueAt {n h : ℕ} (S : Fin n → Option (Fin h)) (i : active S) : Fin h :=
  (S i.1).get (by simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using i.2)

noncomputable def activeFiberEquiv {n h : ℕ} (I : Finset (Fin n)) :
    {S : Fin n → Option (Fin h) // active S = I} ≃ (I → Fin h) where
  toFun S i := valueAt S.1 ⟨i.1,by rw [S.2]; exact i.2⟩
  invFun v := ⟨withSupport I v,active_withSupport I v⟩
  left_inv S := by
    classical
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · have hia : i ∈ active S.1 := S.2.symm ▸ hi
      have hs : (S.1 i).isSome := by simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and] using hia
      obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp hs
      simp only [withSupport,dif_pos hi,valueAt,hj,Option.get_some]
    · have hia : i ∉ active S.1 := by rwa [S.2]
      have hs : S.1 i = none := by
        cases he : S.1 i with
        | none => rfl
        | some j => exact False.elim (hia (by simp [active,he]))
      simp only [withSupport,dif_neg hi,hs]
  right_inv v := by
    classical
    funext i
    simp only [valueAt,withSupport,dif_pos i.2,Option.get_some]

noncomputable def boundedFiberEquiv {n h k : ℕ} (I : BooleanDimension.DegreeIndex n k) :
    {S : DivisionDegreeBasis.DegreeIndex n h k // (⟨active S.1,S.2⟩ : BooleanDimension.DegreeIndex n k) = I} ≃
      {S : Fin n → Option (Fin h) // active S = I.1} where
  toFun S := ⟨S.1.1,congrArg Subtype.val S.2⟩
  invFun S := ⟨⟨S.1,by rw [S.2]; exact I.2⟩,Subtype.ext S.2⟩
  left_inv S := rfl
  right_inv S := rfl

theorem degreeIndex_card (n h k : ℕ) :
    Fintype.card (DivisionDegreeBasis.DegreeIndex n h k) =
      ∑ I : BooleanDimension.DegreeIndex n k, h^I.1.card := by
  classical
  let f : DivisionDegreeBasis.DegreeIndex n h k → BooleanDimension.DegreeIndex n k :=
    fun S => ⟨active S.1,S.2⟩
  calc
    _ = Fintype.card (Σ I : BooleanDimension.DegreeIndex n k, {S : DivisionDegreeBasis.DegreeIndex n h k // f S = I}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ I : BooleanDimension.DegreeIndex n k,
        Fintype.card {S : DivisionDegreeBasis.DegreeIndex n h k // f S = I} := Fintype.card_sigma
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Fintype.card_congr (boundedFiberEquiv (h := h) I),Fintype.card_congr (activeFiberEquiv (h := h) I.1)]
      simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]

theorem HF0_explicit (n h k : ℕ) : HF0 n h k =
    ∑ j ∈ Finset.range (min k n+1), n.choose j * h^j := by
  classical
  rw [DivisionDegreeBasis.HF0_eq_card,degreeIndex_card]
  have he := (BooleanDimension.degreeIndexEquiv n k).sum_comp
    (fun J : (j : Fin (min k n+1)) × {I : Finset (Fin n) // I.card = j.1} => (h^J.1.1 : ℕ))
  change (∑ I : BooleanDimension.DegreeIndex n k, h^I.1.card) = _ at he
  rw [he,Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset_len,Fintype.card_fin,nsmul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => n.choose j * h^j) (min k n+1)

end SemAC02.DivisionDimensionCounts
end

section
-- Inlined Solutions.CumulativeRatios

namespace ProofComplexity.CumulativeRatios

theorem ratio_succ (a b : ℕ → ℝ) (n : ℕ) (hb : ∀ i, 0 ≤ b i) (hb0 : 0 < b 0)
    (hcross : ∀ i ∈ Finset.range (n+1), a (n+1) * b i ≤ a i * b (n+1)) :
    (∑ i ∈ Finset.range (n+2), a i) / (∑ i ∈ Finset.range (n+2), b i) ≤
      (∑ i ∈ Finset.range (n+1), a i) / (∑ i ∈ Finset.range (n+1), b i) := by
  let A := ∑ i ∈ Finset.range (n+1), a i
  let B := ∑ i ∈ Finset.range (n+1), b i
  have hB : 0 < B := hb0.trans_le (Finset.single_le_sum (fun i _ => hb i) (by simp))
  have hB' : 0 < B + b (n+1) := by have := hb (n+1); linarith
  have hc : a (n+1) * B ≤ A * b (n+1) := by
    dsimp [A,B]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum hcross
  have hsumA : (∑ i ∈ Finset.range (n+2), a i) = A + a (n+1) := Finset.sum_range_succ a (n+1)
  have hsumB : (∑ i ∈ Finset.range (n+2), b i) = B + b (n+1) := Finset.sum_range_succ b (n+1)
  rw [hsumA,hsumB]
  change (A+a (n+1))/(B+b (n+1)) ≤ A/B
  apply (div_le_div_iff₀ hB' hB).mpr
  nlinarith

end ProofComplexity.CumulativeRatios
end

section
-- Inlined Solutions.ColoredDownsets

set_option maxHeartbeats 800000

open Finset

namespace SemAC02.ColoredDownsets

def layer {n h : ℕ} (A : Finset (Finset (Fin n × Fin h))) (j : ℕ) :=
  A.filter (fun S => S.card = j)

theorem card_blocks {n h : ℕ} (S : Finset (Fin n × Fin h)) (hS : DivisionSupports.Valid S) :
    (S.image Prod.fst).card = S.card := by
  apply card_image_of_injOn
  rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' he
  dsimp at he
  subst i'
  exact Prod.ext rfl (hS i j j' hij hij')

theorem card_le_blocks {n h : ℕ} (S : Finset (Fin n × Fin h)) (hS : DivisionSupports.Valid S) :
    S.card ≤ n := by
  rw [← card_blocks S hS]
  exact (card_le_univ (S.image Prod.fst)).trans (by simp)

theorem extension_bound {n h : ℕ} (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S) (S : Finset (Fin n × Fin h))
    (hS : DivisionSupports.Valid S) (j : ℕ) (hcard : S.card = j) :
    ((layer A (j+1)).bipartiteAbove (· ⊆ ·) S).card ≤ (n-j)*h := by
  classical
  let U := ((univ \ S.image Prod.fst) ×ˢ (univ : Finset (Fin h)))
  have hU : U.card = (n-j)*h := by
    dsimp only [U]
    rw [Finset.card_product,Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ,Finset.card_univ,Fintype.card_fin,Fintype.card_fin,card_blocks S hS,hcard]
  rw [← hU]
  refine le_trans (card_le_card (t := U.image (fun v => insert v S)) ?_) (card_image_le)
  intro T hT
  simp only [Finset.mem_bipartiteAbove] at hT
  obtain ⟨hTA,hST⟩ := hT
  obtain ⟨hTA,hTc⟩ := mem_filter.mp hTA
  obtain ⟨v,hv,rfl⟩ := exists_eq_insert_iff.mpr ⟨hST,by omega⟩
  apply mem_image.mpr
  refine ⟨v,?_,rfl⟩
  apply mem_product.mpr
  refine ⟨mem_sdiff.mpr ⟨mem_univ _,?_⟩,mem_univ _⟩
  intro hvblock
  obtain ⟨⟨i,j'⟩,hij,he⟩ := mem_image.mp hvblock
  dsimp at he
  have hj : v.2 = j' := hvalid _ hTA v.1 v.2 j' (mem_insert_self _ _) (mem_insert_of_mem (by simpa [he] using hij))
  apply hv
  have heq : v = (i,j') := Prod.ext he.symm hj
  simpa only [heq] using hij

theorem incidence_bound {n h : ℕ} (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S)
    (hdown : ∀ S ∈ A, ∀ T ⊆ S, T ∈ A) (j : ℕ) :
    (layer A (j+1)).card * (j+1) ≤ (layer A j).card * ((n-j)*h) := by
  classical
  apply card_mul_le_card_mul' (· ⊆ ·)
  · intro S hS
    obtain ⟨hSA,hSc⟩ := mem_filter.mp hS
    rw [← hSc,← card_image_of_injOn S.erase_injOn]
    apply card_le_card
    intro T hT
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hT
    simp only [Finset.mem_bipartiteBelow]
    refine ⟨mem_filter.mpr ⟨hdown S hSA _ (erase_subset _ _),?_⟩,erase_subset _ _⟩
    rw [card_erase_of_mem hv,hSc]
    omega
  · intro S hS
    obtain ⟨hSA,hSc⟩ := mem_filter.mp hS
    exact extension_bound A hvalid S (hvalid S hSA) j hSc

end SemAC02.ColoredDownsets
end

section
-- Inlined Solutions.ColoredDownsetRatios

open Finset

namespace SemAC02.ColoredDownsets

def weight (n h j : ℕ) : ℕ := n.choose j * h^j

theorem weight_succ (n h j : ℕ) : weight n h (j+1) * (j+1) = weight n h j * ((n-j)*h) := by
  unfold weight
  rw [pow_succ]
  calc
    n.choose (j+1) * (h^j*h) * (j+1) = (n.choose (j+1)*(j+1)) * h^j * h := by ring
    _ = (n.choose j*(n-j)) * h^j * h := by rw [Nat.choose_succ_right_eq]
    _ = _ := by ring

theorem weight_pos {n h : ℕ} (hh : 1 ≤ h) (j : ℕ) (hj : j ≤ n) : 0 < weight n h j :=
  Nat.mul_pos (Nat.choose_pos hj) (pow_pos (by omega) _)

theorem layer_ratio_succ {n h : ℕ} (hh : 1 ≤ h) (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S)
    (hdown : ∀ S ∈ A, ∀ T ⊆ S, T ∈ A) (j : ℕ) (hj : j < n) :
    ((layer A (j+1)).card : ℝ) / weight n h (j+1) ≤ ((layer A j).card : ℝ) / weight n h j := by
  have hp : (0 : ℝ) < (weight n h (j+1) : ℝ) := by exact_mod_cast weight_pos hh (j+1) (by omega)
  have hp' : (0 : ℝ) < (weight n h j : ℝ) := by exact_mod_cast weight_pos hh j (by omega)
  apply (div_le_div_iff₀ hp hp').mpr
  have hi : ((layer A (j+1)).card : ℝ) * (j+1) ≤ (layer A j).card * (((n-j)*h : ℕ) : ℝ) := by
    exact_mod_cast incidence_bound A hvalid hdown j
  have he : (weight n h (j+1) : ℝ) * (j+1) = (weight n h j : ℝ) * (((n-j)*h : ℕ) : ℝ) := by
    exact_mod_cast weight_succ n h j
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < j+1)).mp
  calc
    ((layer A (j+1)).card : ℝ) * weight n h j * (j+1) =
        (((layer A (j+1)).card : ℝ) * (j+1)) * weight n h j := by ring
    _ ≤ ((layer A j).card * (((n-j)*h : ℕ) : ℝ)) * weight n h j :=
      mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)
    _ = (layer A j).card * ((weight n h j : ℝ) * (((n-j)*h : ℕ) : ℝ)) := by ring
    _ = (layer A j).card * ((weight n h (j+1) : ℝ) * (j+1)) := by rw [he]
    _ = (layer A j).card * weight n h (j+1) * (j+1) := by ring

theorem layer_ratio_antitoneOn {n h : ℕ} (hh : 1 ≤ h) (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S)
    (hdown : ∀ S ∈ A, ∀ T ⊆ S, T ∈ A) :
    AntitoneOn (fun j : ℕ => ((layer A j).card : ℝ) / weight n h j) (Set.Iic n) := by
  intro i hi j hj hij
  have hall : ∀ k, i ≤ k → k ≤ n →
      ((layer A k).card : ℝ) / weight n h k ≤ ((layer A i).card : ℝ) / weight n h i := by
    intro k hki
    induction k,hki using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hki ih =>
      intro hkn
      exact (layer_ratio_succ hh A hvalid hdown k (by omega)).trans (ih (by omega))
  exact hall j hij hj

noncomputable def cumulativeRatio {n h : ℕ} (A : Finset (Finset (Fin n × Fin h))) (k : ℕ) : ℝ :=
  (∑ j ∈ range (k+1), ((layer A j).card : ℝ)) / (∑ j ∈ range (k+1), (weight n h j : ℝ))

theorem cumulative_ratio_succ {n h : ℕ} (hh : 1 ≤ h) (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S)
    (hdown : ∀ S ∈ A, ∀ T ⊆ S, T ∈ A) (k : ℕ) (hk : k < n) :
    cumulativeRatio A (k+1) ≤ cumulativeRatio A k := by
  apply ProofComplexity.CumulativeRatios.ratio_succ
    (fun j => ((layer A j).card : ℝ)) (fun j => (weight n h j : ℝ)) k
    (fun _ => Nat.cast_nonneg _) (by simp [weight])
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
  have hp : (0 : ℝ) < (weight n h (k+1) : ℝ) := by exact_mod_cast weight_pos hh (k+1) (by omega)
  have hp' : (0 : ℝ) < (weight n h j : ℝ) := by exact_mod_cast weight_pos hh j (by omega)
  exact (div_le_div_iff₀ hp hp').mp (layer_ratio_antitoneOn hh A hvalid hdown
    (show j ≤ n from by omega) (show k+1 ≤ n from by omega) (by omega : j ≤ k+1))

theorem cumulative_ratio_antitoneOn {n h : ℕ} (hh : 1 ≤ h) (A : Finset (Finset (Fin n × Fin h)))
    (hvalid : ∀ S ∈ A, DivisionSupports.Valid S)
    (hdown : ∀ S ∈ A, ∀ T ⊆ S, T ∈ A) :
    AntitoneOn (cumulativeRatio A) (Set.Iic n) := by
  intro i hi j hj hij
  have hall : ∀ k, i ≤ k → k ≤ n → cumulativeRatio A k ≤ cumulativeRatio A i := by
    intro k hki
    induction k,hki using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hki ih =>
      intro hkn
      exact (cumulative_ratio_succ hh A hvalid hdown k (by omega)).trans (ih (by omega))
  exact hall j hij hj

theorem cumulative_card {n h : ℕ} (A : Finset (Finset (Fin n × Fin h))) (k : ℕ) :
    (A.filter (fun S => S.card ≤ k)).card = ∑ j ∈ range (k+1), (layer A j).card := by
  have he := sum_card_fiberwise_eq_card_filter A (range (k+1)) (fun S => S.card)
  simpa only [mem_range,Nat.lt_succ_iff,layer] using he.symm

end SemAC02.ColoredDownsets
end

section
-- Inlined Solutions.DivisionNormalizedRank

open Module Finset

namespace SemAC02.DivisionNormalizedRank

noncomputable def imageRank {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) : ℕ :=
  finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) a))

theorem rank_eq_count {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    imageRank a k = ((DivisionStandardFamily.family a).filter (fun S => S.card ≤ k)).card := by
  classical
  rw [imageRank,DivisionStandardFamily.rank_eq_card]
  exact Fintype.card_of_subtype _ (fun S => Finset.mem_filter)

theorem rank_eq_sum {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    imageRank a k = ∑ j ∈ range (k+1), (ColoredDownsets.layer (DivisionStandardFamily.family a) j).card := by
  rw [rank_eq_count,ColoredDownsets.cumulative_card]

theorem ratio_eq {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) (hk : k ≤ n) :
    (imageRank a k : ℝ) / HF0 n h k = ColoredDownsets.cumulativeRatio (DivisionStandardFamily.family a) k := by
  rw [rank_eq_sum,DivisionDimensionCounts.HF0_explicit,min_eq_left hk]
  simp only [Nat.cast_sum,ColoredDownsets.cumulativeRatio,ColoredDownsets.weight,Nat.cast_mul,Nat.cast_pow]

/-- Normalised rank monotonicity, Lemma 4.11 of the semantic paper. -/
theorem ratio_antitoneOn {n h : ℕ} (hh : 1 ≤ h) (a : nDivOmega n h → ZMod 2) :
    AntitoneOn (fun k => (imageRank a k : ℝ) / HF0 n h k) (Set.Iic n) := by
  intro i hi j hj hij
  dsimp only
  rw [ratio_eq a i hi,ratio_eq a j hj]
  apply ColoredDownsets.cumulative_ratio_antitoneOn hh (DivisionStandardFamily.family a)
    (fun S hS => ((DivisionStandardFamily.mem_family a S).mp hS).1)
    (DivisionStandardFamily.family_downward a) hi hj hij

theorem normalized_rank_mono {n h : ℕ} (hh : 1 ≤ h) (a : nDivOmega n h → ZMod 2)
    (j k : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) :
    (imageRank a k : ℝ) / HF0 n h k ≤ (imageRank a j : ℝ) / HF0 n h j :=
  ratio_antitoneOn hh a (hjk.trans hkn) hkn hjk

theorem HF0_pos (n h k : ℕ) : 0 < HF0 n h k := by
  rw [DivisionDimensionCounts.HF0_explicit]
  have he := single_le_sum (f := fun j => n.choose j * h^j) (fun j _ => Nat.zero_le _) (by simp : 0 ∈ range (min k n+1))
  exact Nat.lt_of_succ_le (by simpa using he)

theorem rank_stable {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) (hk : n ≤ k) :
    imageRank a k = imageRank a n := by
  classical
  rw [rank_eq_count,rank_eq_count]
  congr 1
  ext S
  simp only [mem_filter]
  have hSn : S ∈ DivisionStandardFamily.family a → S.card ≤ n := fun hS =>
    ColoredDownsets.card_le_blocks S ((DivisionStandardFamily.mem_family a S).mp hS).1
  constructor
  · intro hS
    exact ⟨hS.1,hSn hS.1⟩
  · intro hS
    exact ⟨hS.1,(hSn hS.1).trans hk⟩

theorem HF0_stable (n h k : ℕ) (hk : n ≤ k) : HF0 n h k = HF0 n h n := by
  rw [DivisionDimensionCounts.HF0_explicit,DivisionDimensionCounts.HF0_explicit,min_eq_right hk,min_self]

theorem ratio_min {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) :
    (imageRank a k : ℝ) / HF0 n h k = (imageRank a (min k n) : ℝ) / HF0 n h (min k n) := by
  by_cases hk : k ≤ n
  · rw [min_eq_left hk]
  · have hkn : n ≤ k := by omega
    rw [min_eq_right hkn,rank_stable a k hkn,HF0_stable n h k hkn]

/-- The ratio remains constant once the degree reaches the number of blocks. -/
theorem ratio_antitone {n h : ℕ} (hh : 1 ≤ h) (a : nDivOmega n h → ZMod 2) :
    Antitone (fun k => (imageRank a k : ℝ) / HF0 n h k) := by
  intro j k hjk
  dsimp only
  rw [ratio_min a j,ratio_min a k]
  exact ratio_antitoneOn hh a (Nat.min_le_right _ _) (Nat.min_le_right _ _) (by omega)

end SemAC02.DivisionNormalizedRank
end

section
-- Inlined Solutions.DivisionFunctionAlgebra

open MvPolynomial

namespace SemAC02.DivisionFunctionAlgebra

@[simp] theorem restriction_one (n h : ℕ) : restrOmega n h 1 = 1 := by
  funext X
  simp only [SingletonDivision.restrOmega_apply,map_one,Pi.one_apply]

@[simp] theorem restriction_mul {n h : ℕ} (p q : MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    restrOmega n h (p*q) = restrOmega n h p * restrOmega n h q := by
  funext X
  simp only [SingletonDivision.restrOmega_apply,map_mul,Pi.mul_apply]

@[simp] theorem restriction_prod {n h : ℕ} {I : Type*} (E : Finset I)
    (p : I → MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    restrOmega n h (∏ i ∈ E, p i) = ∏ i ∈ E, restrOmega n h (p i) := by
  classical
  induction E using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,restriction_one]
  | @insert i E hi ih => simp only [Finset.prod_insert hi,restriction_mul,ih]

theorem degree_mono {n h i j : ℕ} (hij : i ≤ j) : BleF0 n h i ≤ BleF0 n h j := by
  rintro f ⟨p,hp,rfl⟩
  refine ⟨p,(mem_restrictTotalDegree _ _ _).mpr ?_,rfl⟩
  exact ((mem_restrictTotalDegree _ _ _).mp hp).trans hij

theorem degree_mul {n h i j : ℕ} {f g : nDivOmega n h → ZMod 2}
    (hf : f ∈ BleF0 n h i) (hg : g ∈ BleF0 n h j) : f*g ∈ BleF0 n h (i+j) := by
  obtain ⟨p,hp,rfl⟩ := hf
  obtain ⟨q,hq,rfl⟩ := hg
  refine ⟨p*q,(mem_restrictTotalDegree _ _ _).mpr ?_,restriction_mul p q⟩
  exact (totalDegree_mul p q).trans (Nat.add_le_add ((mem_restrictTotalDegree _ _ _).mp hp)
    ((mem_restrictTotalDegree _ _ _).mp hq))

theorem span_one_add_degree {n h w : ℕ} {J : Type*}
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    Submodule.span (ZMod 2) (Set.range (fun j => 1+gs j)) ≤ restrictTotalDegree _ _ w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  apply (mem_restrictTotalDegree _ _ _).mpr
  exact (totalDegree_add 1 (gs j)).trans (max_le (by simp) (hgs j))

end SemAC02.DivisionFunctionAlgebra
end

section
-- Inlined Solutions.FiniteFunctionColumns

open Module Function Submodule

namespace ProofComplexity.FiniteFunctionColumns

/-- Independent functions admit a full-size independent set of evaluation columns. -/
theorem exists_columns {K X I : Type*} [Field K] [Fintype X] [Fintype I]
    (v : I → X → K) (hv : LinearIndependent K v) :
    ∃ S : Set X, Nat.card S = Fintype.card I ∧
      LinearIndependent K (fun x : S => fun i => v i x.1) := by
  classical
  obtain ⟨S,_,_,hspan,hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K (fun x i => v i x)) (Set.empty_subset (Set.univ : Set X))
  have hfull : span K (Set.range (fun x : S => fun i => v i x.1)) = ⊤ := by
    apply top_unique
    rw [← span_flip_eq_top_iff_linearIndependent.mpr hv]
    apply span_le.mpr
    rintro z ⟨x,rfl⟩
    have hz := hspan (Set.mem_image_of_mem (fun x i => v i x) (Set.mem_univ x))
    apply (show span K ((fun x i => v i x) '' S) ≤ span K (Set.range (fun x : S => fun i => v i x.1)) from ?_) hz
    apply span_mono
    rintro z ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  let b : Basis S K (I → K) := Basis.mk hli (ge_of_eq hfull)
  refine ⟨S,?_,hli⟩
  rw [Nat.card_eq_fintype_card]
  exact (finrank_eq_card_basis b).symm.trans (finrank_fintype_fun_eq_card K)

/-- Keeping selected nonzero evaluation columns lower-bounds the rank after multiplication. -/
theorem surviving_columns_le_rank {X I : Type*} [Fintype X] [Fintype I]
    (v : I → X → ZMod 2) (S : Set X)
    (hS : LinearIndependent (ZMod 2) (fun x : S => fun i => v i x.1)) (q : X → ZMod 2) :
    Nat.card {x : S // q x.1 = 1} ≤
      finrank (ZMod 2) (span (ZMod 2) (Set.range (fun i => q * v i))) := by
  classical
  let A : Matrix I X (ZMod 2) := fun i x => q x * v i x
  let Y := {x : S // q x.1 = 1}
  let B : Matrix Y I (ZMod 2) := fun y i => v i y.1.1
  have hB : LinearIndependent (ZMod 2) B.row := hS.comp (fun y : Y => y.1) Subtype.val_injective
  have he : (A.submatrix id (fun y : Y => y.1.1)).transpose = B := by
    ext y i
    change q y.1.1 * v i y.1.1 = v i y.1.1
    rw [y.2,one_mul]
  have hb := Matrix.rank_submatrix_le A id (fun y : Y => y.1.1)
  rw [← Matrix.rank_transpose (A.submatrix id (fun y : Y => y.1.1)),he,hB.rank_matrix] at hb
  rw [Matrix.rank_eq_finrank_span_row] at hb
  have hrow : A.row = (fun i => q * v i) := by funext i x; rfl
  rw [hrow] at hb
  simpa only [Nat.card_eq_fintype_card,Y] using hb

end ProofComplexity.FiniteFunctionColumns
end

section
-- Inlined Solutions.F2Averaging

open Finset

namespace ProofComplexity.F2Averaging

theorem twice_point_hits {X : Type*} [Fintype X] (W : Submodule (ZMod 2) (X → ZMod 2))
    [Fintype W] (x : X) (u : W) (hu : u.1 x = 1) :
    2 * (∑ q : W, if q.1 x = 1 then 1 else 0 : ℕ) = Fintype.card W := by
  classical
  let f : W → ℕ := fun q => if q.1 x = 1 then 1 else 0
  have he := Equiv.sum_comp (Equiv.addRight u) f
  change (∑ q : W, f (q+u)) = ∑ q : W, f q at he
  have hp : ∀ q : W, f (q+u) + f q = 1 := by
    intro q
    rcases AC02Frege.MajorityFoundation.eq_zero_or_one (q.1 x) with hq | hq
    · simp [f,hu,hq]
    · norm_num [f,hu,hq,show (2 : ZMod 2) ≠ 1 by decide]
  change 2 * (∑ q : W, f q) = _
  calc
    _ = ∑ q : W, (f (q+u)+f q) := by rw [sum_add_distrib,he]; omega
    _ = ∑ _q : W, 1 := sum_congr rfl (fun q _ => hp q)
    _ = Fintype.card W := by simp

/-- A finite F₂ space that detects every selected point has a member hitting half of them. -/
theorem exists_half_hits {X P : Type*} [Fintype X] [Fintype P]
    (W : Submodule (ZMod 2) (X → ZMod 2)) (e : P → X)
    (hW : ∀ p, ∃ u : W, u.1 (e p) = 1) :
    ∃ q : W, Fintype.card P ≤ 2 * (univ.filter (fun p : P => q.1 (e p) = 1)).card := by
  classical
  let score : W → ℕ := fun q => ∑ p : P, if q.1 (e p) = 1 then 1 else 0
  have he : 2 * (∑ q : W, score q) = Fintype.card W * Fintype.card P := by
    dsimp only [score]
    rw [sum_comm,mul_sum]
    calc
      (∑ p : P, 2 * ∑ q : W, if q.1 (e p) = 1 then 1 else 0) = ∑ _p : P, Fintype.card W := by
        apply sum_congr rfl
        intro p _
        obtain ⟨u,hu⟩ := hW p
        exact twice_point_hits W (e p) u hu
      _ = _ := by simp [mul_comm]
  have hscore : ∀ q : W, score q = (univ.filter (fun p : P => q.1 (e p) = 1)).card := by
    intro q
    simp only [score,card_eq_sum_ones,sum_filter]
  by_contra! hn
  have hn' : ∀ q : W, 2 * score q < Fintype.card P := by simpa only [hscore] using hn
  have hs := sum_lt_sum (fun q (_ : q ∈ (univ : Finset W)) => (hn' q).le)
    ⟨(0 : W),mem_univ _,hn' 0⟩
  rw [← mul_sum,he] at hs
  simpa only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,lt_self_iff_false] using hs

end ProofComplexity.F2Averaging
end

section
-- Inlined Solutions.FunctionRankHalving

open Module Submodule Finset

namespace ProofComplexity.FunctionRankHalving

/-- A detecting F₂ space contains a multiplier retaining at least half a function space's rank. -/
theorem exists_half_rank {X : Type*} [Fintype X]
    (V W : Submodule (ZMod 2) (X → ZMod 2))
    (hdetect : ∀ x, (∃ v : V, v.1 x ≠ 0) → ∃ u : W, u.1 x = 1) :
    ∃ q : W, finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (V.map (LinearMap.mulLeft (ZMod 2) q.1)) := by
  classical
  let b := Module.finBasis (ZMod 2) V
  let v : Fin (finrank (ZMod 2) V) → X → ZMod 2 := fun i => (b i).1
  have hv : LinearIndependent (ZMod 2) v := b.linearIndependent.map' V.subtype V.ker_subtype
  obtain ⟨S,hcard,hS⟩ := FiniteFunctionColumns.exists_columns v hv
  have hdet : ∀ x : S, ∃ u : W, u.1 x.1 = 1 := by
    intro x
    apply hdetect x.1
    by_contra! hz
    apply hS.ne_zero x
    funext i
    exact hz (b i)
  obtain ⟨q,hq⟩ := F2Averaging.exists_half_hits W (fun x : S => x.1) hdet
  have hcard' : Fintype.card S = finrank (ZMod 2) V := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hcard
  rw [hcard'] at hq
  have hhits : (univ.filter (fun x : S => q.1 x.1 = 1)).card = Nat.card {x : S // q.1 x.1 = 1} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hhits] at hq
  have hrank := FiniteFunctionColumns.surviving_columns_le_rank v S hS q.1
  have hle : span (ZMod 2) (Set.range (fun i => q.1 * v i)) ≤ V.map (LinearMap.mulLeft (ZMod 2) q.1) := by
    apply span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨v i,(b i).2,rfl⟩
  exact ⟨q,hq.trans (Nat.mul_le_mul_left 2 (hrank.trans (Submodule.finrank_mono hle)))⟩

theorem complement_rank_bound {X : Type*} [Fintype X]
    (V U : Submodule (ZMod 2) (X → ZMod 2)) (q : X → ZMod 2)
    (hUV : U ≤ V) (hkill : ∀ u ∈ U, (1+q)*u = 0) :
    finrank (ZMod 2) (V.map (LinearMap.mulLeft (ZMod 2) (1+q))) + finrank (ZMod 2) U ≤ finrank (ZMod 2) V := by
  let L := (LinearMap.mulLeft (ZMod 2) (1+q)).domRestrict V
  have hUker : U ≤ L.ker.map V.subtype := by
    intro u hu
    refine ⟨⟨u,hUV hu⟩,?_,rfl⟩
    exact hkill u hu
  have hdim := Submodule.finrank_mono hUker
  rw [Submodule.finrank_map_subtype_eq] at hdim
  have hnull := L.finrank_range_add_finrank_ker
  have hrange : L.range = V.map (LinearMap.mulLeft (ZMod 2) (1+q)) := LinearMap.range_domRestrict _ _
  rw [hrange] at hnull
  omega

/-- Multiplication by the complementary Boolean factor removes at least half the smaller rank. -/
theorem exists_rank_decrease {X : Type*} [Fintype X]
    (Vsmall Vbig W : Submodule (ZMod 2) (X → ZMod 2))
    (hdetect : ∀ x, (∃ v : Vsmall, v.1 x ≠ 0) → ∃ u : W, u.1 x = 1)
    (hmap : ∀ q : W, Vsmall.map (LinearMap.mulLeft (ZMod 2) q.1) ≤ Vbig) :
    ∃ q : W, 2 * finrank (ZMod 2) (Vbig.map (LinearMap.mulLeft (ZMod 2) (1+q.1))) +
      finrank (ZMod 2) Vsmall ≤ 2 * finrank (ZMod 2) Vbig := by
  obtain ⟨q,hq⟩ := exists_half_rank Vsmall W hdetect
  have hkill : ∀ u ∈ Vsmall.map (LinearMap.mulLeft (ZMod 2) q.1), (1+q.1)*u = 0 := by
    rintro u ⟨v,_,rfl⟩
    funext x
    change (1+q.1 x)*(q.1 x*v x) = 0
    rcases AC02Frege.MajorityFoundation.eq_zero_or_one (q.1 x) with hx | hx
    · simp only [hx,mul_zero,zero_mul]
    · rw [hx,show (1 : ZMod 2)+1 = 0 by decide,zero_mul]
  have hc := complement_rank_bound Vbig (Vsmall.map (LinearMap.mulLeft (ZMod 2) q.1)) q.1 (hmap q) hkill
  exact ⟨q,by omega⟩

end ProofComplexity.FunctionRankHalving
end

section
-- Inlined Solutions.ProductRankDecrease

set_option maxHeartbeats 1000000

open Module MvPolynomial Submodule
open SemAC02.DivisionNormalizedRank SemAC02.DivisionFunctionAlgebra

namespace SemAC02.ProductRankDecrease

/-- The integer rank decrease underlying Claim 4.12, with a polynomial in the required span. -/
theorem exists_integer_decrease {n h w k : ℕ} (hwk : w ≤ k) {J : Type*} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w)
    (b : nDivOmega n h → ZMod 2) (hb : b * restrOmega n h (∏ j, gs j) = 0) :
    ∃ q : MvPolynomial (Fin n × Fin h) (ZMod 2),
      q ∈ span (ZMod 2) (Set.range (fun j => 1+gs j)) ∧
      2 * imageRank (b*(1+restrOmega n h q)) k + imageRank b (k-w) ≤ 2 * imageRank b k := by
  classical
  let P := span (ZMod 2) (Set.range (fun j => 1+gs j))
  let W := P.map (restrOmega n h)
  let Vsmall := (BleF0 n h (k-w)).map (LinearMap.mulLeft (ZMod 2) b)
  let Vbig := (BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) b)
  have hdetect : ∀ X, (∃ v : Vsmall, v.1 X ≠ 0) → ∃ u : W, u.1 X = 1 := by
    intro X hv
    obtain ⟨v,hv⟩ := hv
    obtain ⟨f,_,hfv⟩ := v.2
    have hne : b X * f X ≠ 0 := by
      change (LinearMap.mulLeft (ZMod 2) b f) X ≠ 0
      rw [hfv]
      exact hv
    have hbX : b X ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have htX : restrOmega n h (∏ j, gs j) X = 0 :=
      (mul_eq_zero.mp (congrFun hb X)).resolve_left hbX
    rw [restriction_prod] at htX
    simp only [Finset.prod_apply] at htX
    obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp htX
    refine ⟨⟨restrOmega n h (1+gs j),⟨1+gs j,subset_span ⟨j,rfl⟩,rfl⟩⟩,?_⟩
    simp only [map_add,restriction_one,Pi.add_apply,Pi.one_apply,hj,add_zero]
  have hmap : ∀ q : W, Vsmall.map (LinearMap.mulLeft (ZMod 2) q.1) ≤ Vbig := by
    intro q
    have hqdeg : q.1 ∈ BleF0 n h w := by
      obtain ⟨p,hp,hpq⟩ := q.2
      exact ⟨p,span_one_add_degree gs hgs hp,hpq⟩
    rintro g ⟨v,⟨f,hf,hfv⟩,hvg⟩
    refine ⟨q.1*f,degree_mono (by omega : w+(k-w) ≤ k) (degree_mul hqdeg hf),?_⟩
    rw [← hvg,← hfv]
    funext X
    change b X * (q.1 X * f X) = q.1 X * (b X * f X)
    ring
  obtain ⟨q,hq⟩ := ProofComplexity.FunctionRankHalving.exists_rank_decrease Vsmall Vbig W hdetect hmap
  have he : Vbig.map (LinearMap.mulLeft (ZMod 2) (1+q.1)) =
      (BleF0 n h k).map (LinearMap.mulLeft (ZMod 2) (b*(1+q.1))) := by
    dsimp only [Vbig]
    rw [← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro f
    funext X
    change (1+q.1 X)*(b X*f X) = (b X*(1+q.1 X))*f X
    ring
  rw [he] at hq
  obtain ⟨p,hp,hpq⟩ := q.2
  refine ⟨p,hp,?_⟩
  rw [← hpq] at hq
  exact hq

/-- Claim 4.12: normalisation turns the integer rank decrease into a geometric factor. -/
theorem exists_normalized_decrease {n h w k : ℕ} (hh : 1 ≤ h) (hwk : w ≤ k) (hkn : k ≤ n)
    {J : Type*} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w)
    (b : nDivOmega n h → ZMod 2) (hb : b * restrOmega n h (∏ j, gs j) = 0) :
    ∃ q : MvPolynomial (Fin n × Fin h) (ZMod 2),
      q ∈ span (ZMod 2) (Set.range (fun j => 1+gs j)) ∧
      (imageRank (b*(1+restrOmega n h q)) k : ℝ) ≤
        (1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ))) * imageRank b k := by
  obtain ⟨q,hq,hdec⟩ := exists_integer_decrease hwk gs hgs b hb
  refine ⟨q,hq,?_⟩
  have hH : (0 : ℝ) < HF0 n h k := by exact_mod_cast HF0_pos n h k
  have hHsmall : (0 : ℝ) < HF0 n h (k-w) := by exact_mod_cast HF0_pos n h (k-w)
  have hnorm := (div_le_div_iff₀ hH hHsmall).mp
    (normalized_rank_mono hh b (k-w) k (by omega) hkn)
  have hdec' : 2 * (imageRank (b*(1+restrOmega n h q)) k : ℝ) + imageRank b (k-w) ≤ 2 * imageRank b k := by
    exact_mod_cast hdec
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 2*(HF0 n h k : ℝ))).mp
  have he : (1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ))) * imageRank b k * (2*(HF0 n h k : ℝ)) =
      2*(HF0 n h k : ℝ)*imageRank b k - (HF0 n h (k-w) : ℝ)*imageRank b k := by
    field_simp [ne_of_gt hH]
    <;> ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hdec' hH.le]

end SemAC02.ProductRankDecrease
end

section
-- Inlined Solutions.ProductApproximationIteration

set_option maxHeartbeats 1000000

open Module MvPolynomial Submodule
open SemAC02.DivisionNormalizedRank SemAC02.DivisionFunctionAlgebra

namespace SemAC02.ProductApproximationIteration

theorem HF0_mono (n h : ℕ) {i j : ℕ} (hij : i ≤ j) : HF0 n h i ≤ HF0 n h j :=
  Submodule.finrank_mono (degree_mono hij)

theorem imageRank_le {n h : ℕ} (a : nDivOmega n h → ZMod 2) (k : ℕ) : imageRank a k ≤ HF0 n h k :=
  Submodule.finrank_map_le _ _

theorem decay_nonneg (n h w k : ℕ) :
    0 ≤ 1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ)) := by
  have hp : (0 : ℝ) < HF0 n h k := by exact_mod_cast HF0_pos n h k
  have hm : (HF0 n h (k-w) : ℝ) ≤ HF0 n h k := by exact_mod_cast HF0_mono n h (Nat.sub_le _ _)
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(HF0 n h k : ℝ))).mpr
  linarith

theorem product_kills_span {n h : ℕ} {J : Type*} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2))
    (q : MvPolynomial (Fin n × Fin h) (ZMod 2))
    (hq : q ∈ span (ZMod 2) (Set.range (fun j => 1+gs j))) :
    restrOmega n h (∏ j, gs j) * restrOmega n h q = 0 := by
  classical
  let L := (LinearMap.mulLeft (ZMod 2) (restrOmega n h (∏ j, gs j))).comp (restrOmega n h)
  have hspan : span (ZMod 2) (Set.range (fun j => 1+gs j)) ≤ L.ker := by
    apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    change restrOmega n h (∏ i, gs i) * restrOmega n h (1+gs j) = 0
    funext X
    simp only [restriction_prod,map_add,restriction_one,Finset.prod_apply,Pi.mul_apply,Pi.add_apply,Pi.one_apply,Pi.zero_apply]
    rcases AC02Frege.MajorityFoundation.eq_zero_or_one (restrOmega n h (gs j) X) with hj | hj
    · rw [show (∏ i, restrOmega n h (gs i) X) = 0 from Finset.prod_eq_zero (Finset.mem_univ j) hj,zero_mul]
    · rw [hj,show (1 : ZMod 2)+1 = 0 by decide,mul_zero]
  exact hspan hq

theorem exists_geometric_approximation {n h w k : ℕ} (hh : 1 ≤ h) (hwk : w ≤ k) (hkn : k ≤ n)
    {J : Type*} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) (r : ℕ) :
    ∃ q : Fin r → MvPolynomial (Fin n × Fin h) (ZMod 2),
      (∀ l, q l ∈ span (ZMod 2) (Set.range (fun j => 1+gs j))) ∧
      (∏ l, (1+q l)).totalDegree ≤ r*w ∧
      restrOmega n h ((∏ l, (1+q l))*(∏ j, gs j)) = restrOmega n h (∏ j, gs j) ∧
      (imageRank (restrOmega n h ((∏ j, gs j)+(∏ l, (1+q l)))) k : ℝ) ≤
        (HF0 n h k : ℝ) * (1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ)))^r := by
  classical
  let t := restrOmega n h (∏ j, gs j)
  let ρ := 1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ))
  have hρ : 0 ≤ ρ := decay_nonneg n h w k
  induction r with
  | zero =>
    refine ⟨Fin.elim0,(by intro l; exact Fin.elim0 l),?_,?_,?_⟩
    · simp only [Finset.univ_eq_empty,Finset.prod_empty,totalDegree_one,Nat.zero_mul,le_refl]
    · simp only [Finset.univ_eq_empty,Finset.prod_empty,one_mul]
    · simpa only [pow_zero,mul_one] using
        (Nat.cast_le.mpr (imageRank_le (restrOmega n h ((∏ j, gs j)+(∏ l : Fin 0, (1+Fin.elim0 l)))) k) :
          (imageRank (restrOmega n h ((∏ j, gs j)+(∏ l : Fin 0, (1+Fin.elim0 l)))) k : ℝ) ≤ HF0 n h k)
  | succ r ih =>
    obtain ⟨q,hq,hdeg,hagree,hrank⟩ := ih
    let A := ∏ l, (1+q l)
    let a := restrOmega n h A
    have hat : a*t = t := by simpa only [restriction_mul] using hagree
    have hbt : (t+a)*t = 0 := by
      rw [add_mul,hat]
      have htt : t*t = t := by
        funext X
        rcases AC02Frege.MajorityFoundation.eq_zero_or_one (t X) with hx | hx <;> simp [Pi.mul_apply,hx]
      rw [htt]
      funext X
      exact CharTwo.add_self_eq_zero (t X)
    obtain ⟨u,hu,hstep⟩ := ProductRankDecrease.exists_normalized_decrease hh hwk hkn gs hgs (t+a) hbt
    let q' : Fin (r+1) → MvPolynomial (Fin n × Fin h) (ZMod 2) := Fin.cons u q
    have hprod : (∏ l, (1+q' l)) = (1+u)*A := by
      rw [Fin.prod_univ_succ]
      simp only [q',Fin.cons_zero,Fin.cons_succ,A]
    have hudeg : u.totalDegree ≤ w := (mem_restrictTotalDegree _ _ _).mp (span_one_add_degree gs hgs hu)
    have hufac : (1+u).totalDegree ≤ w := (totalDegree_add 1 u).trans (max_le (by simp) hudeg)
    have hkill := product_kills_span gs u hu
    change t * restrOmega n h u = 0 at hkill
    have herror : t + restrOmega n h ((1+u)*A) = (t+a)*(1+restrOmega n h u) := by
      rw [restriction_mul,map_add,restriction_one]
      change t+(1+restrOmega n h u)*a = (t+a)*(1+restrOmega n h u)
      symm
      calc
        _ = t+(1+restrOmega n h u)*a+t*restrOmega n h u := by ring
        _ = _ := by rw [hkill,add_zero]
    refine ⟨q',?_,?_,?_,?_⟩
    · intro l
      refine Fin.cases ?_ (fun i => ?_) l
      · exact hu
      · exact hq i
    · rw [hprod]
      exact (totalDegree_mul _ _).trans ((Nat.add_le_add hufac hdeg).trans (by rw [Nat.add_mul,one_mul]; omega))
    · rw [hprod,restriction_mul,restriction_mul,map_add,restriction_one]
      change ((1+restrOmega n h u)*a)*t = t
      calc
        _ = a*t+a*(t*restrOmega n h u) := by ring
        _ = _ := by rw [hat,hkill,mul_zero,add_zero]
    · rw [hprod,map_add]
      change (imageRank (t+restrOmega n h ((1+u)*A)) k : ℝ) ≤ (HF0 n h k : ℝ)*ρ^(r+1)
      rw [herror]
      change (imageRank ((t+a)*(1+restrOmega n h u)) k : ℝ) ≤ ρ*imageRank (t+a) k at hstep
      have hrank' : (imageRank (t+a) k : ℝ) ≤ (HF0 n h k : ℝ)*ρ^r := by
        simpa only [map_add] using hrank
      calc
        _ ≤ ρ*imageRank (t+a) k := hstep
        _ ≤ ρ*((HF0 n h k : ℝ)*ρ^r) := mul_le_mul_of_nonneg_left hrank' hρ
        _ = _ := by rw [pow_succ]; ring

end SemAC02.ProductApproximationIteration
end

section
-- Inlined Solutions.ProductApproximationNumerics

set_option maxHeartbeats 1000000

open Finset
open SemAC02.ColoredDownsets

namespace SemAC02.ProductApproximationNumerics

theorem layer_doubles {n h : ℕ} (hh : 1 ≤ h) (j : ℕ) (hj : 3*(j+1) ≤ n) :
    2*weight n h j ≤ weight n h (j+1) := by
  have hfac : 2*(j+1) ≤ (n-j)*h := by
    have hm : n-j ≤ (n-j)*h := by simpa only [mul_one] using Nat.mul_le_mul_left (n-j) hh
    omega
  have hrec : (weight n h (j+1) : ℝ)*(j+1) = (weight n h j : ℝ)*(((n-j)*h : ℕ) : ℝ) := by
    exact_mod_cast weight_succ n h j
  have hi : (weight n h j : ℝ)*(2*(j+1)) ≤ (weight n h j : ℝ)*(((n-j)*h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left (weight n h j) hfac
  have hr : 2*(weight n h j : ℝ) ≤ weight n h (j+1) := by nlinarith
  exact_mod_cast hr

theorem partial_sum_bound {n h : ℕ} (hh : 1 ≤ h) (k : ℕ) (hk : 3*k ≤ n) :
    (∑ j ∈ range (k+1), weight n h j) ≤ 2*weight n h k := by
  revert hk
  induction k with
  | zero => intro _; simp [weight]
  | succ k ih =>
    intro hk
    rw [sum_range_succ]
    have hp := ih (by omega)
    have hd := layer_doubles hh k hk
    omega

theorem HF0_upper {n h : ℕ} (hh : 1 ≤ h) (k : ℕ) (hk : 3*k ≤ n) :
    HF0 n h k ≤ 2*weight n h k := by
  rw [DivisionDimensionCounts.HF0_explicit,min_eq_left (by omega : k ≤ n)]
  exact partial_sum_bound hh k hk

theorem layer_le_HF0 {n h : ℕ} (k : ℕ) (hk : k ≤ n) : weight n h k ≤ HF0 n h k := by
  rw [DivisionDimensionCounts.HF0_explicit,min_eq_left hk]
  exact single_le_sum (fun j _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self k))

noncomputable def beta (n h k : ℕ) : ℝ := (k : ℝ)/(2*((n*h : ℕ) : ℝ))

theorem beta_nonneg (n h k : ℕ) : 0 ≤ beta n h k := by unfold beta; positivity

theorem beta_layer_step {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (k j : ℕ)
    (hkj : k ≤ 2*(j+1)) :
    beta n h k * (weight n h (j+1) : ℝ) ≤ weight n h j := by
  have hN : (0 : ℝ) < ((n*h : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < h)
  have hrec : (weight n h (j+1) : ℝ)*(j+1) = (weight n h j : ℝ)*(((n-j)*h : ℕ) : ℝ) := by
    exact_mod_cast weight_succ n h j
  have hfac : (((n-j)*h : ℕ) : ℝ) ≤ ((n*h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right h (Nat.sub_le n j)
  have hkj' : (k : ℝ) ≤ 2*(j+1) := by exact_mod_cast hkj
  unfold beta
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*((n*h : ℕ) : ℝ))).mpr
  have hmul := mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg (weight n h j) : (0 : ℝ) ≤ _)
  have hmul' := mul_le_mul_of_nonneg_right hkj' (Nat.cast_nonneg (weight n h (j+1)) : (0 : ℝ) ≤ _)
  nlinarith

theorem beta_power_layers {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (k j r : ℕ)
    (hkj : k ≤ 2*(j+1)) :
    beta n h k ^ r * (weight n h (j+r) : ℝ) ≤ weight n h j := by
  induction r with
  | zero => simp only [pow_zero,Nat.add_zero,one_mul,le_refl]
  | succ r ih =>
    have hs := beta_layer_step hn hh k (j+r) (by omega)
    calc
      _ = beta n h k ^ r * (beta n h k * (weight n h (j+r+1) : ℝ)) := by simp only [Nat.add_succ,pow_succ]; ring
      _ ≤ beta n h k ^ r * (weight n h (j+r) : ℝ) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg (beta_nonneg n h k) r)
      _ ≤ _ := ih

/-- The explicit lower bound on alpha used in the paper's final estimate. -/
theorem alpha_lower {n h w k : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hw : 2*w ≤ k) (hk : 3*k ≤ n) :
    (1/4 : ℝ)*beta n h k^w ≤ (HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ)) := by
  have hH : (0 : ℝ) < HF0 n h k := by exact_mod_cast DivisionNormalizedRank.HF0_pos n h k
  have hu : (HF0 n h k : ℝ) ≤ 2*(weight n h k : ℝ) := by exact_mod_cast HF0_upper hh k hk
  have hl : (weight n h (k-w) : ℝ) ≤ HF0 n h (k-w) := by exact_mod_cast layer_le_HF0 (h := h) (k-w) (by omega)
  have hp := beta_power_layers hn hh k (k-w) w (by omega)
  rw [Nat.sub_add_cancel (by omega : w ≤ k)] at hp
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(HF0 n h k : ℝ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hu (pow_nonneg (beta_nonneg n h k) w)]

end SemAC02.ProductApproximationNumerics
end

section
-- Inlined Solutions.ProductApproximation

set_option maxHeartbeats 1000000

open Module MvPolynomial
open SemAC02.DivisionNormalizedRank SemAC02.ProductApproximationNumerics

namespace SemAC02.ProductApproximation

theorem geometric_explicit_bound {n h w k : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hw : 2*w ≤ k) (hk : 3*k ≤ n) (r : ℕ) :
    (HF0 n h k : ℝ)*(1-(HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ)))^r ≤
      2*(n.choose k : ℝ)*(h : ℝ)^k / Real.exp ((r : ℝ)/4*beta n h k^w) := by
  let α := (HF0 n h (k-w) : ℝ)/(2*(HF0 n h k : ℝ))
  have hρ : 0 ≤ 1-α := ProductApproximationIteration.decay_nonneg n h w k
  have hH : (0 : ℝ) ≤ HF0 n h k := Nat.cast_nonneg _
  have he : 1-α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
  have hp := pow_le_pow_left₀ hρ he r
  rw [← Real.exp_nat_mul] at hp
  have hp' : (1-α)^r ≤ Real.exp (-((r : ℝ)*α)) := by simpa only [mul_neg] using hp
  have hα : (1/4 : ℝ)*beta n h k^w ≤ α := alpha_lower hn hh hw hk
  have heα : -((r : ℝ)*α) ≤ -((r : ℝ)/4*beta n h k^w) := by
    nlinarith [mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg r : (0 : ℝ) ≤ _)]
  have hHu : (HF0 n h k : ℝ) ≤ 2*(n.choose k : ℝ)*(h : ℝ)^k := by
    have hu : HF0 n h k ≤ 2*n.choose k*h^k := by
      simpa only [ColoredDownsets.weight,mul_assoc] using HF0_upper hh k hk
    exact_mod_cast hu
  calc
    _ ≤ (HF0 n h k : ℝ)*Real.exp (-((r : ℝ)*α)) := mul_le_mul_of_nonneg_left hp' hH
    _ ≤ (2*(n.choose k : ℝ)*(h : ℝ)^k)*Real.exp (-((r : ℝ)/4*beta n h k^w)) :=
      mul_le_mul hHu (Real.exp_le_exp.mpr heα) (Real.exp_nonneg _) (by positivity)
    _ = _ := by simp only [Real.exp_neg,div_eq_mul_inv]

theorem product_approximation (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (w k r : ℕ)
    (hw : 1 ≤ w) (hwk : w ≤ k) (hkn : k ≤ n) {J : Type} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    ∃ q : Fin r → MvPolynomial (Fin n × Fin h) (ZMod 2),
      (∀ l, q l ∈ Submodule.span (ZMod 2) (Set.range fun j => 1 + gs j)) ∧
      (∏ l, (1 + q l)).totalDegree ≤ r * w ∧
      restrOmega n h ((∏ l, (1 + q l)) * ∏ j, gs j) = restrOmega n h (∏ j, gs j) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
        (HF0 n h k : ℝ) * (1 - (HF0 n h (k - w) : ℝ) / (2 * (HF0 n h k : ℝ))) ^ r ∧
      (2 * w ≤ k → 3 * k ≤ n →
        (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
          2 * (n.choose k : ℝ) * (h : ℝ) ^ k /
            Real.exp ((r : ℝ) / 4 * ((k : ℝ) / (2 * ((n * h : ℕ) : ℝ))) ^ w))  := by
  obtain ⟨q,hq,hdeg,hkeep,hgeo⟩ := ProductApproximationIteration.exists_geometric_approximation hh hwk hkn gs hgs r
  refine ⟨q,hq,hdeg,hkeep,hgeo,?_⟩
  intro hw2 hk3
  exact hgeo.trans (geometric_explicit_bound hn hh hw2 hk3 r)

end SemAC02.ProductApproximation
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_4_9_product_approximation
namespace SemAC02

open MvPolynomial

/-- **Lemma 4.9 (Approximation of T)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 4.9, p.30): let `n, h ≥ 1` be
integers, put `N = nh`, and partition the variables into `V₁, …, V_n`, each of size `h`. Let `F₀`
consist of all products `xy` of distinct variables in the same part, and work in
`B_{F₀} = B_N/⟨F₀⟩`. Let `1 ≤ w ≤ k ≤ n` and `r ≥ 0` be integers, and let `T = ∏_{j∈J} g_j`,
where `deg(g_j) ≤ w` for each `j ∈ J`. Then there exist `q₁, …, q_r ∈ span{1 + g_j : j ∈ J}`
such that the approximator `a := ∏_{ℓ=1}^r (1 + q_ℓ)` has degree at most `rw` and satisfies
`aT = T`. Define the error polynomial `err_T := T + a` and the error operator
`Err_T : B_{F₀}^{≤k} → B_{F₀}`, `Err_T(f) := f err_T`. Then
`rank(Err_T) = dim(err_T B_{F₀}^{≤k}) ≤ H_{F₀}(k) (1 − H_{F₀}(k − w)/(2H_{F₀}(k)))^r`.
If additionally `2w ≤ k ≤ n/3`, then
`rank(Err_T) ≤ 2 C(n,k) h^k / exp((r/4)(k/(2N))^w)`.

**Formalization Note** The variables are `Fin n × Fin h` (part `i` is `{i} × Fin h`); `B_{F₀}` is
the space of functions on `Ω` (at most one `1` per part), an element being restricted from any
polynomial representing it (`restrOmega`), and degree is the least total degree of a
representative. The `g_j` are given by representatives of total degree `≤ w`, `J` a finite type;
`q_ℓ` are taken in the span of the representatives `1 + g_j`. `err_T B_{F₀}^{≤k}` is the image of
`B_{F₀}^{≤k}` under multiplication by `err_T`; `k ≤ n/3` is `3k ≤ n`. -/
theorem lemma_4_9_product_approximation (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (w k r : ℕ)
    (hw : 1 ≤ w) (hwk : w ≤ k) (hkn : k ≤ n) {J : Type} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    ∃ q : Fin r → MvPolynomial (Fin n × Fin h) (ZMod 2),
      (∀ l, q l ∈ Submodule.span (ZMod 2) (Set.range fun j => 1 + gs j)) ∧
      (∏ l, (1 + q l)).totalDegree ≤ r * w ∧
      restrOmega n h ((∏ l, (1 + q l)) * ∏ j, gs j) = restrOmega n h (∏ j, gs j) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
        (HF0 n h k : ℝ) * (1 - (HF0 n h (k - w) : ℝ) / (2 * (HF0 n h k : ℝ))) ^ r ∧
      (2 * w ≤ k → 3 * k ≤ n →
        (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
          2 * (n.choose k : ℝ) * (h : ℝ) ^ k /
            Real.exp ((r : ℝ) / 4 * ((k : ℝ) / (2 * ((n * h : ℕ) : ℝ))) ^ w)) := by
  exact SemAC02.ProductApproximation.product_approximation n h hn hh w k r hw hwk hkn gs hgs

end SemAC02
end

section
-- Inlined Solutions.BooleanProductApproximation

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.SingletonDivision SemAC02.BooleanDimension

namespace SemAC02.BooleanProductApproximation

theorem rename_back {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2)) :
    rename Prod.fst (rename (fun i => (i,(0 : Fin 1))) p) = p := by
  rw [rename_rename]
  exact rename_id_apply p

theorem Hn_mono (n : ℕ) : Monotone (Hn n) := by
  intro j k hjk
  rw [← finrank_Ble n j, ← finrank_Ble n k]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨A,hA,rfl⟩
  exact ⟨A,hA.trans hjk,rfl⟩

theorem power_decay (α : ℝ) (hα : α ≤ 1) (r : ℕ) :
    (1-α)^r ≤ Real.exp (-((r : ℝ)*α)) := by
  have he : 1-α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-α) he r
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_neg] using hp

theorem product_approximation {n : ℕ} (hn : 1 ≤ n) (w k r : ℕ)
    (hw : 1 ≤ w) (hwk : w ≤ k) (hkn : k ≤ n) {J : Type} [Fintype J]
    (gs : J → MvPolynomial (Fin n) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    ∃ a : MvPolynomial (Fin n) (ZMod 2), a.totalDegree ≤ r*w ∧
      (finrank (ZMod 2) (multSpace ((∏ j,gs j)+a) k) : ℝ) ≤
        (Hn n k : ℝ) * Real.exp (-((r : ℝ) * ((Hn n (k-w) : ℝ)/(2*(Hn n k : ℝ))))) := by
  classical
  let gsL : J → MvPolynomial (Fin n × Fin 1) (ZMod 2) :=
    fun j => rename (fun i => (i,(0 : Fin 1))) (gs j)
  obtain ⟨q,hq,hdeg,hprod,hrank,_⟩ := lemma_4_9_product_approximation n 1 hn (by omega) w k r
    hw hwk hkn gsL (fun j => (totalDegree_rename_le _ _).trans (hgs j))
  let a := rename Prod.fst (∏ l, (1+q l))
  refine ⟨a,(totalDegree_rename_le _ _).trans hdeg,?_⟩
  have herr : rename Prod.fst ((∏ j,gsL j)+∏ l,(1+q l)) = (∏ j,gs j)+a := by
    rw [map_add,map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact rename_back (gs j)
  rw [finrank_error, herr, HF0_one, HF0_one] at hrank
  have hH : (0 : ℝ) < (Hn n k : ℝ) := by exact_mod_cast Hn_pos n k
  have hmono : (Hn n (k-w) : ℝ) ≤ (Hn n k : ℝ) := by
    exact_mod_cast Hn_mono n (Nat.sub_le k w)
  have hα : (Hn n (k-w) : ℝ)/(2*(Hn n k : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(Hn n k : ℝ))).mpr
    linarith
  exact hrank.trans (mul_le_mul_of_nonneg_left (power_decay _ hα r) hH.le)

end SemAC02.BooleanProductApproximation
end

section
-- Inlined Solutions.CircuitApproximationChoice

open Module MvPolynomial AC02Frege

namespace SemAC02.CircuitApproximationChoice

noncomputable def select {n : ℕ} (w k t : ℕ) (ps : List (MvPolynomial (Fin n) (ZMod 2))) :
    MvPolynomial (Fin n) (ZMod 2) := Classical.epsilon (fun a => a.totalDegree ≤ t*w ∧
      (finrank (ZMod 2) (multSpace (ps.prod+a) k) : ℝ) ≤
        (Hn n k : ℝ) * Real.exp (-((t : ℝ)*((Hn n (k-w) : ℝ)/(2*(Hn n k : ℝ))))))

theorem select_spec {n : ℕ} (hn : 1 ≤ n) (w k t : ℕ) (hw : 1 ≤ w) (hwk : w ≤ k) (hkn : k ≤ n)
    (ps : List (MvPolynomial (Fin n) (ZMod 2))) (hps : ∀ p ∈ ps, p.totalDegree ≤ w) :
    (select w k t ps).totalDegree ≤ t*w ∧
      (finrank (ZMod 2) (multSpace (ps.prod+select w k t ps) k) : ℝ) ≤
        (Hn n k : ℝ) * Real.exp (-((t : ℝ)*((Hn n (k-w) : ℝ)/(2*(Hn n k : ℝ))))) := by
  classical
  unfold select
  have h := BooleanProductApproximation.product_approximation hn w k t hw hwk hkn
    (fun i : Fin ps.length => ps[i]) (fun i => hps _ (List.getElem_mem i.2))
  have he : (∏ i : Fin ps.length, ps[i]) = ps.prod := by
    rw [← List.prod_ofFn]
    exact congrArg List.prod (List.ofFn_getElem (xs := ps))
  rw [he] at h
  exact Classical.epsilon_spec h

theorem list_sum_degree {n : ℕ} (ps : List (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (hps : ∀ p ∈ ps, p.totalDegree ≤ D) : ps.sum.totalDegree ≤ D := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.sum_cons]
    exact (totalDegree_add _ _).trans (max_le (hps p (by simp)) (ih (fun q hq => hps q (by simp [hq]))))

end SemAC02.CircuitApproximationChoice
end

section
-- Inlined Solutions.CircuitApproximants

open Module MvPolynomial AC02Frege
open SemAC02.CircuitApproximationChoice

namespace SemAC02.CircuitApproximants

def weight {n : ℕ} (r : ℕ) (A : Circ (Fin n)) : ℕ := r ^ (A.depth-1)

def repetitions {n : ℕ} (d r R : ℕ) (A : Circ (Fin n)) : ℕ := if A.depth = d then R else r

noncomputable def approx {n : ℕ} (d r R k : ℕ) : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2)
  | .const b => arithRaw (.const b)
  | .lit v b => arithRaw (.lit v b)
  | .and cs => 1 + select (weight r (.and cs)) k (repetitions d r R (.and cs))
      (cs.map (fun c => 1 + approx d r R k c))
  | .or cs => select (weight r (.or cs)) k (repetitions d r R (.or cs))
      (cs.map (fun c => approx d r R k c))
  | .xor cs => 1 + (cs.map (fun c => 1 + approx d r R k c)).sum

noncomputable def nodeRaw {n : ℕ} (d r R k : ℕ) : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2)
  | .const b => arithRaw (.const b)
  | .lit v b => arithRaw (.lit v b)
  | .and cs => 1 + (cs.map (fun c => 1 + approx d r R k c)).prod
  | .or cs => (cs.map (fun c => approx d r R k c)).prod
  | .xor cs => 1 + (cs.map (fun c => 1 + approx d r R k c)).sum

noncomputable def err {n : ℕ} (d r R k : ℕ) (A : Circ (Fin n)) : MvPolynomial (Fin n) (ZMod 2) :=
  approx d r R k A + nodeRaw d r R k A

theorem depth_mem_le {n : ℕ} (cs : List (Circ (Fin n))) (c : Circ (Fin n)) (hc : c ∈ cs) :
    c.depth ≤ (cs.map Circ.depth).foldr max 0 := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_max_left _ _
    · exact (ih hc).trans (le_max_right _ _)

theorem weight_pos {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (A : Circ (Fin n)) : 1 ≤ weight r A :=
  one_le_pow₀ hr

theorem selected_bound {n : ℕ} (d r R : ℕ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (A : Circ (Fin n)) (hA : 1 ≤ A.depth) :
    repetitions d r R A * weight r A = if A.depth = d then R*r^(d-1) else r^A.depth := by
  unfold repetitions weight
  split_ifs with he
  · rw [he]
  · calc
      r * r^(A.depth-1) = r^((A.depth-1)+1) := by rw [pow_succ, Nat.mul_comm]
      _ = r^A.depth := congrArg (fun j => r^j) (by omega)

set_option maxHeartbeats 800000 in
theorem approx_degree {n : ℕ} (d r R k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (hrk : r^(d-1) ≤ k) (hkn : k ≤ n) (A : Circ (Fin n)) (hA : A.depth ≤ d) :
    (approx d r R k A).totalDegree ≤ if A.depth = d then R*r^(d-1) else r^A.depth := by
  have hn : 1 ≤ n := (one_le_pow₀ hr).trans (hrk.trans hkn)
  have hall : ∀ A : Circ (Fin n), A.depth ≤ d →
      (approx d r R k A).totalDegree ≤ if A.depth = d then R*r^(d-1) else r^A.depth := by
    intro A
    induction A using (measure (fun A : Circ (Fin n) => A.depth)).wf.induction with
    | h A ih =>
      intro hA
      cases A with
      | const b =>
        cases b <;> simp [approx,arithRaw,Circ.depth,show ¬ (0 = d) by omega]
      | lit v b =>
        cases b
        · simp [approx,arithRaw,Circ.depth,show ¬ (0 = d) by omega]
        · simp only [approx,arithRaw,Circ.depth,if_neg (show ¬ (0=d) by omega),pow_zero,↓reduceIte]
          exact (totalDegree_add _ _).trans (by simp)
      | and cs =>
        have hchildren : ∀ c ∈ cs, (approx d r R k c).totalDegree ≤ weight r (Circ.and cs) := by
          intro c hc
          have hcd : c.depth < (Circ.and cs).depth := by
            simp only [Circ.depth]
            exact Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          have hcD : c.depth < d := lt_of_lt_of_le hcd hA
          have hdeg := ih c hcd (by omega)
          rw [if_neg (ne_of_lt hcD)] at hdeg
          exact hdeg.trans (Nat.pow_le_pow_right hr (by omega))
        have hwk : weight r (Circ.and cs) ≤ k :=
          (Nat.pow_le_pow_right hr (by omega)).trans hrk
        have hs := select_spec hn (weight r (Circ.and cs)) k (repetitions d r R (Circ.and cs)) (weight_pos r hr _) hwk hkn
          (cs.map (fun c => 1+approx d r R k c)) (by
            intro p hp
            obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
            exact (totalDegree_add _ _).trans (by simpa using hchildren c hc))
        have hnode : 1 ≤ (Circ.and cs).depth := by simp [Circ.depth]
        rw [approx]
        change (1+select _ k _ _).totalDegree ≤ _
        apply (totalDegree_add _ _).trans
        simpa only [totalDegree_one,zero_le,max_eq_right,selected_bound d r R hr hR _ hnode] using hs.1
      | or cs =>
        have hchildren : ∀ c ∈ cs, (approx d r R k c).totalDegree ≤ weight r (Circ.or cs) := by
          intro c hc
          have hcd : c.depth < (Circ.or cs).depth := by
            simp only [Circ.depth]
            exact Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          have hcD : c.depth < d := lt_of_lt_of_le hcd hA
          have hdeg := ih c hcd (by omega)
          rw [if_neg (ne_of_lt hcD)] at hdeg
          exact hdeg.trans (Nat.pow_le_pow_right hr (by omega))
        have hwk : weight r (Circ.or cs) ≤ k :=
          (Nat.pow_le_pow_right hr (by omega)).trans hrk
        have hs := select_spec hn (weight r (Circ.or cs)) k (repetitions d r R (Circ.or cs)) (weight_pos r hr _) hwk hkn
          (cs.map (fun c => approx d r R k c)) (by
            intro p hp
            obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
            exact hchildren c hc)
        have hnode : 1 ≤ (Circ.or cs).depth := by simp [Circ.depth]
        simpa only [approx,selected_bound d r R hr hR _ hnode] using hs.1
      | xor cs =>
        have hchildren : ∀ c ∈ cs, (approx d r R k c).totalDegree ≤ weight r (Circ.xor cs) := by
          intro c hc
          have hcd : c.depth < (Circ.xor cs).depth := by
            simp only [Circ.depth]
            exact Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          have hcD : c.depth < d := lt_of_lt_of_le hcd hA
          have hdeg := ih c hcd (by omega)
          rw [if_neg (ne_of_lt hcD)] at hdeg
          exact hdeg.trans (Nat.pow_le_pow_right hr (by omega))
        have hsum : ((cs.map (fun c => 1+approx d r R k c)).sum).totalDegree ≤ weight r (Circ.xor cs) :=
          list_sum_degree _ _ (by
            intro p hp
            obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
            exact (totalDegree_add _ _).trans (by simpa using hchildren c hc))
        have hb : weight r (Circ.xor cs) ≤ if (Circ.xor cs).depth = d then R*r^(d-1) else r^(Circ.xor cs).depth := by
          unfold weight
          split_ifs with he
          · rw [he]; nlinarith [one_le_pow₀ (n := d-1) hr]
          · exact Nat.pow_le_pow_right hr (Nat.sub_le _ _)
        rw [approx]
        change (1+(cs.map (fun c => 1+approx d r R k c)).sum).totalDegree ≤ _
        apply (totalDegree_add _ _).trans
        simpa only [totalDegree_one] using (max_le (Nat.zero_le _) hsum).trans hb
  exact hall A hA

end SemAC02.CircuitApproximants
end

section
-- Inlined Solutions.CircuitApproximationErrorBounds

open Module MvPolynomial AC02Frege
open SemAC02.CircuitApproximationChoice SemAC02.BooleanProductApproximation

namespace SemAC02.CircuitApproximants

noncomputable def theta (n d r R k : ℕ) : ℝ :=
  min ((r : ℝ)*((Hn n (k-r^(d-2)) : ℝ)/(2*(Hn n k : ℝ))))
    ((R : ℝ)*((Hn n (k-r^(d-1)) : ℝ)/(2*(Hn n k : ℝ))))

theorem approx_degree_below {n : ℕ} (d r R k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (hrk : r^(d-1) ≤ k) (hkn : k ≤ n) (j : ℕ) (hj : j ≤ d)
    (A : Circ (Fin n)) (hA : A.depth < j) : (approx d r R k A).totalDegree ≤ r^(j-1) := by
  have hdeg := approx_degree d r R k hd hr hR hrk hkn A (by omega)
  rw [if_neg (by omega : A.depth ≠ d)] at hdeg
  exact hdeg.trans (Nat.pow_le_pow_right hr (by omega))

theorem rate_le {n : ℕ} (d r R k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (A : Circ (Fin n)) (hA0 : 1 ≤ A.depth) (hAd : A.depth ≤ d) :
    theta n d r R k ≤ (repetitions d r R A : ℝ) *
      ((Hn n (k-weight r A) : ℝ)/(2*(Hn n k : ℝ))) := by
  unfold repetitions weight theta
  split_ifs with he
  · simpa only [he] using min_le_right
      ((r : ℝ)*((Hn n (k-r^(d-2)) : ℝ)/(2*(Hn n k : ℝ))))
      ((R : ℝ)*((Hn n (k-r^(d-1)) : ℝ)/(2*(Hn n k : ℝ))))
  · have hpow : r^(A.depth-1) ≤ r^(d-2) := Nat.pow_le_pow_right hr (by omega)
    have hcount := Hn_mono n (Nat.sub_le_sub_left hpow k)
    have hcountR : (Hn n (k-r^(d-2)) : ℝ) ≤ (Hn n (k-r^(A.depth-1)) : ℝ) := by exact_mod_cast hcount
    exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hcountR (by positivity)) (Nat.cast_nonneg r))

theorem multSpace_zero (n k : ℕ) : multSpace (0 : MvPolynomial (Fin n) (ZMod 2)) k = ⊥ := by
  apply le_antisymm
  · rintro p ⟨q,hq,rfl⟩
    change mulML 0 q = 0
    simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply,zero_mul,map_zero]
  · exact bot_le

theorem err_rank {n : ℕ} (d r R k : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (hrk : r^(d-1) ≤ k) (hkn : k ≤ n) (A : Circ (Fin n)) (hA : A.depth ≤ d) :
    (finrank (ZMod 2) (multSpace (err d r R k A) k) : ℝ) ≤
      (Hn n k : ℝ)*Real.exp (-theta n d r R k) := by
  classical
  have hn : 1 ≤ n := (one_le_pow₀ hr).trans (hrk.trans hkn)
  have hnonneg : (0 : ℝ) ≤ (Hn n k : ℝ)*Real.exp (-theta n d r R k) := by positivity
  cases A with
  | const b =>
    have he : err (n := n) d r R k (Circ.const b) = 0 := by unfold err; rw [approx,nodeRaw,CharTwo.add_self_eq_zero]
    rw [he,multSpace_zero,finrank_bot]
    simpa only [Nat.cast_zero] using hnonneg
  | lit v b =>
    have he : err d r R k (Circ.lit v b) = 0 := by unfold err; rw [approx,nodeRaw,CharTwo.add_self_eq_zero]
    rw [he,multSpace_zero,finrank_bot]
    simpa only [Nat.cast_zero] using hnonneg
  | xor cs =>
    have he : err d r R k (Circ.xor cs) = 0 := by unfold err; rw [approx,nodeRaw,CharTwo.add_self_eq_zero]
    rw [he,multSpace_zero,finrank_bot]
    simpa only [Nat.cast_zero] using hnonneg
  | and cs =>
    have hnode : 1 ≤ (Circ.and cs).depth := by simp [Circ.depth]
    have hwk : weight r (Circ.and cs) ≤ k := (Nat.pow_le_pow_right hr (by omega)).trans hrk
    have hchildren : ∀ p ∈ cs.map (fun c => 1+approx d r R k c), p.totalDegree ≤ weight r (Circ.and cs) := by
      intro p hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      have hcd : c.depth < (Circ.and cs).depth := by
        simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
      exact (totalDegree_add _ _).trans (by
        simpa only [weight,totalDegree_one,zero_le,max_eq_right] using (approx_degree_below d r R k hd hr hR hrk hkn _ hA c hcd))
    have hs := (select_spec hn (weight r (Circ.and cs)) k (repetitions d r R (Circ.and cs)) (weight_pos r hr _) hwk hkn _ hchildren).2
    have he : err d r R k (Circ.and cs) =
        (cs.map (fun c => 1+approx d r R k c)).prod+
          select (weight r (Circ.and cs)) k (repetitions d r R (Circ.and cs)) (cs.map (fun c => 1+approx d r R k c)) := by
      unfold err
      rw [approx,nodeRaw]
      generalize select (weight r (Circ.and cs)) k (repetitions d r R (Circ.and cs)) (cs.map (fun c => 1+approx d r R k c)) = a
      generalize (cs.map (fun c => 1+approx d r R k c)).prod = b
      calc
        (1+a)+(1+b) = (1+1)+(b+a) := by ring
        _ = b+a := by rw [CharTwo.add_self_eq_zero,zero_add]
    rw [he]
    exact hs.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (rate_le d r R k hd hr _ hnode hA))) (Nat.cast_nonneg _))
  | or cs =>
    have hnode : 1 ≤ (Circ.or cs).depth := by simp [Circ.depth]
    have hwk : weight r (Circ.or cs) ≤ k := (Nat.pow_le_pow_right hr (by omega)).trans hrk
    have hchildren : ∀ p ∈ cs.map (fun c => approx d r R k c), p.totalDegree ≤ weight r (Circ.or cs) := by
      intro p hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      exact approx_degree_below d r R k hd hr hR hrk hkn _ hA c
        (by simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc))
    have hs := (select_spec hn (weight r (Circ.or cs)) k (repetitions d r R (Circ.or cs)) (weight_pos r hr _) hwk hkn _ hchildren).2
    have he : err d r R k (Circ.or cs) = (cs.map (fun c => approx d r R k c)).prod+
        select (weight r (Circ.or cs)) k (repetitions d r R (Circ.or cs)) (cs.map (fun c => approx d r R k c)) := by
      unfold err
      rw [approx,nodeRaw,add_comm]
    rw [he]
    exact hs.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (rate_le d r R k hd hr _ hnode hA))) (Nat.cast_nonneg _))

end SemAC02.CircuitApproximants
end

section
-- Inlined Solutions.CircuitSubcircuits

namespace SemAC02.CircuitSubcircuits

open CircuitApproximants Classical

theorem mem_children_union {n : ℕ} (cs : List (Circ (Fin n))) (B : Circ (Fin n)) :
    B ∈ (cs.map Circ.subcircuits).foldr (· ∪ ·) ∅ ↔ ∃ c ∈ cs, B ∈ c.subcircuits := by
  classical
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.foldr_cons,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨c',hc',hB⟩)
      · exact ⟨c,Or.inl rfl,h⟩
      · exact ⟨c',Or.inr hc',hB⟩
    · rintro ⟨c',(rfl | hc'),hB⟩
      · exact Or.inl hB
      · exact Or.inr ⟨c',hc',hB⟩

theorem node_properties {n : ℕ} (A : Circ (Fin n)) (cs : List (Circ (Fin n)))
    (hroot : A.subcircuits = insert A ((cs.map Circ.subcircuits).foldr (· ∪ ·) ∅))
    (hdepth : ∀ c ∈ cs, c.depth < A.depth)
    (ih : ∀ c ∈ cs, ∀ B ∈ c.subcircuits, B.depth ≤ c.depth ∧ B.subcircuits ⊆ c.subcircuits) :
    ∀ B ∈ A.subcircuits, B.depth ≤ A.depth ∧ B.subcircuits ⊆ A.subcircuits := by
  classical
  intro B hB
  rw [hroot,Finset.mem_insert] at hB
  rcases hB with rfl | hB
  · exact ⟨le_rfl,Finset.Subset.refl _⟩
  obtain ⟨c,hc,hBc⟩ := (mem_children_union cs B).mp hB
  obtain ⟨hBd,hBs⟩ := ih c hc B hBc
  refine ⟨hBd.trans (hdepth c hc).le,hBs.trans ?_⟩
  intro C hC
  rw [hroot]
  exact Finset.mem_insert_of_mem ((mem_children_union cs C).mpr ⟨c,hc,hC⟩)

theorem properties {n : ℕ} (A : Circ (Fin n)) :
    ∀ B ∈ A.subcircuits, B.depth ≤ A.depth ∧ B.subcircuits ⊆ A.subcircuits := by
  classical
  induction A using (measure (fun A : Circ (Fin n) => A.depth)).wf.induction with
  | h A ih =>
    cases A with
    | const b =>
      intro B hB
      have he : B = Circ.const b := by simpa only [Circ.subcircuits,Finset.mem_singleton] using hB
      subst B
      exact ⟨le_rfl,Finset.Subset.refl _⟩
    | lit v b =>
      intro B hB
      have he : B = Circ.lit v b := by simpa only [Circ.subcircuits,Finset.mem_singleton] using hB
      subst B
      exact ⟨le_rfl,Finset.Subset.refl _⟩
    | and cs =>
      apply node_properties (Circ.and cs) cs (by rw [Circ.subcircuits])
      · exact fun c hc => (by simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc))
      · intro c hc
        have hcd : c.depth < (Circ.and cs).depth := by
          simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
        exact ih c hcd
    | or cs =>
      apply node_properties (Circ.or cs) cs (by rw [Circ.subcircuits])
      · exact fun c hc => (by simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc))
      · intro c hc
        have hcd : c.depth < (Circ.or cs).depth := by
          simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
        exact ih c hcd
    | xor cs =>
      apply node_properties (Circ.xor cs) cs (by rw [Circ.subcircuits])
      · exact fun c hc => (by simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc))
      · intro c hc
        have hcd : c.depth < (Circ.xor cs).depth := by
          simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
        exact ih c hcd

theorem self_mem {n : ℕ} (A : Circ (Fin n)) : A ∈ A.subcircuits := by
  classical
  cases A <;> simp only [Circ.subcircuits,Finset.mem_insert,Finset.mem_singleton,true_or]

theorem child_subset {n : ℕ} (A : Circ (Fin n)) (cs : List (Circ (Fin n)))
    (hroot : A.subcircuits = insert A ((cs.map Circ.subcircuits).foldr (· ∪ ·) ∅))
    (c : Circ (Fin n)) (hc : c ∈ cs) : c.subcircuits ⊆ A.subcircuits := by
  intro B hB
  rw [hroot]
  exact Finset.mem_insert_of_mem ((mem_children_union cs B).mpr ⟨c,hc,hB⟩)

end SemAC02.CircuitSubcircuits
end

section
-- Inlined Solutions.CircuitSemantics

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.CircuitSemantics

theorem arithmetic_and (bs : List Bool) :
    1 + (bs.map (fun b => 1 + (if b then 0 else 1 : ZMod 2))).prod =
      if bs.all id then 0 else 1 := by
  induction bs with
  | nil => simp [CharTwo.add_self_eq_zero]
  | cons b bs ih =>
    cases b <;> simp only [List.map_cons, List.prod_cons, List.all_cons, id_eq,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      CharTwo.add_self_eq_zero, zero_mul, add_zero, one_mul] at *
    exact ih

theorem arithmetic_or (bs : List Bool) :
    (bs.map (fun b : Bool => (if b then 0 else 1 : ZMod 2))).prod =
      if bs.any id then 0 else 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp [ih]

theorem arithmetic_xor (bs : List Bool) :
    1 + (bs.map (fun b => 1 + (if b then 0 else 1 : ZMod 2))).sum =
      if bs.foldr Bool.xor false then 0 else 1 := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases h : bs.foldr Bool.xor false <;> cases b <;>
      simp [h, List.map_cons, List.sum_cons, CharTwo.add_self_eq_zero] at ih ⊢ <;> simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add] using ih

theorem arithRaw_eval {V : Type} (A : Circ V) (X : V → Bool) :
    eval (toF2 X) (arithRaw A) = if A.eval X then 0 else 1 := by
  cases A with
  | const b => cases b <;> simp [arithRaw, Circ.eval]
  | lit v b => cases b <;> cases h : X v <;> simp [arithRaw, Circ.eval, toF2, h, CharTwo.add_self_eq_zero]
  | and cs =>
    simp only [arithRaw, map_add, map_one, map_list_prod, List.map_map, Function.comp_def]
    have he : cs.map (fun c => 1 + eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b => 1 + (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_and]
    simp only [Circ.eval]
  | or cs =>
    simp only [arithRaw, map_list_prod, List.map_map, Function.comp_def]
    have he : cs.map (fun c => eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b : Bool => (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_or]
    simp only [Circ.eval]
  | xor cs =>
    simp only [arithRaw, map_add, map_one, map_list_sum, List.map_map, Function.comp_def]
    have he : cs.map (fun c => 1 + eval (toF2 X) (arithRaw c)) =
        (cs.map (fun c => c.eval X)).map (fun b => 1 + (if b then 0 else 1 : ZMod 2)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hc
      rw [arithRaw_eval c X]
      rfl
    rw [he, arithmetic_xor]
    simp only [Circ.eval]
termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

@[simp] theorem arith_eval {V : Type} (A : Circ V) (X : V → Bool) :
    eval (toF2 X) (arith A) = if A.eval X then 0 else 1 := by
  rw [arith, eval_ml, arithRaw_eval]

theorem eval_rename {V W : Type} (A : Circ V) (f : V → W) (X : W → Bool) :
    (A.rename f).eval X = A.eval (fun v => X (f v)) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => simp [Circ.rename, Circ.eval]
  | and cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | or cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | xor cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem eval_flip {V : Type} (A : Circ V) (X : V → Bool) :
    A.flip.eval X = A.eval (fun v => !X v) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => cases b <;> simp [Circ.flip, Circ.eval]
  | and cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | or cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | xor cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

theorem eval_orChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.orChildren.map (fun c => c.eval X)).any id = A.eval X := by
  cases A <;> simp [Circ.orChildren, Circ.eval]

theorem eval_andChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.andChildren.map (fun c => c.eval X)).all id = A.eval X := by
  cases A <;> simp [Circ.andChildren, Circ.eval]

theorem eval_liftAxiom {n m : ℕ} (g : Circ (Fin m))
    (C : LiftSAParity.Clause (Fin n))
    (α : Fin n × Bool → Fin g.andChildren.length) (X : Fin n × Fin m → Bool) :
    (liftAxiom g C α).eval X = true ↔
      ∃ l ∈ C, (gadgetH g l.2 (α l)).eval (fun j => X (l.1, j)) = true := by
  classical
  simp only [liftAxiom, Circ.eval, List.map_flatMap, List.any_flatMap]
  simp only [List.map_map, Function.comp_def, eval_rename]
  simp only [eval_orChildren, List.any_eq_true, Finset.mem_toList]


end SemAC02.CircuitSemantics
end

section
-- Inlined Solutions.CircuitApproximationAgreement

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.BooleanFunctionPolynomials SemAC02.CircuitSubcircuits

namespace SemAC02.CircuitApproximants

theorem eval_agreement {n : ℕ} (d r R k : ℕ) (x : Fin n → Bool) (A : Circ (Fin n))
    (herr : ∀ B ∈ A.subcircuits, eval (toF2 x) (err d r R k B) = 0) :
    eval (toF2 x) (approx d r R k A) = eval (toF2 x) (arithRaw A) := by
  have hall : ∀ A : Circ (Fin n),
      (∀ B ∈ A.subcircuits, eval (toF2 x) (err d r R k B) = 0) →
      eval (toF2 x) (approx d r R k A) = eval (toF2 x) (arithRaw A) := by
    intro A
    induction A using (measure (fun A : Circ (Fin n) => A.depth)).wf.induction with
    | h A ih =>
      intro herr
      have hlocal := herr A (self_mem A)
      unfold err at hlocal
      rw [map_add] at hlocal
      have he : eval (toF2 x) (approx d r R k A) = eval (toF2 x) (nodeRaw d r R k A) := by
        apply add_right_cancel (b := eval (toF2 x) (nodeRaw d r R k A))
        rw [CharTwo.add_self_eq_zero]
        exact hlocal
      cases A with
      | const b => exact he
      | lit v b => exact he
      | and cs =>
        have hc : ∀ c ∈ cs, eval (toF2 x) (approx d r R k c) = eval (toF2 x) (arithRaw c) := by
          intro c hc
          have hcd : c.depth < (Circ.and cs).depth := by
            simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          exact ih c hcd (fun B hB => herr B (child_subset (Circ.and cs) cs (by rw [Circ.subcircuits]) c hc hB))
        rw [he]
        simp only [nodeRaw,arithRaw,map_add,map_one,map_list_prod,List.map_map,Function.comp_def]
        congr 2
        apply List.map_congr_left
        intro c hcs
        rw [hc c hcs]
      | or cs =>
        have hc : ∀ c ∈ cs, eval (toF2 x) (approx d r R k c) = eval (toF2 x) (arithRaw c) := by
          intro c hc
          have hcd : c.depth < (Circ.or cs).depth := by
            simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          exact ih c hcd (fun B hB => herr B (child_subset (Circ.or cs) cs (by rw [Circ.subcircuits]) c hc hB))
        rw [he]
        simp only [nodeRaw,arithRaw,map_list_prod,List.map_map,Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro c hcs
        exact hc c hcs
      | xor cs =>
        have hc : ∀ c ∈ cs, eval (toF2 x) (approx d r R k c) = eval (toF2 x) (arithRaw c) := by
          intro c hc
          have hcd : c.depth < (Circ.xor cs).depth := by
            simpa only [Circ.depth] using Nat.lt_one_add_iff.mpr (depth_mem_le cs c hc)
          exact ih c hcd (fun B hB => herr B (child_subset (Circ.xor cs) cs (by rw [Circ.subcircuits]) c hc hB))
        rw [he]
        simp only [nodeRaw,arithRaw,map_add,map_one,map_list_sum,List.map_map,Function.comp_def]
        congr 2
        apply List.map_congr_left
        intro c hcs
        rw [hc c hcs]
  exact hall A herr

theorem multiplied_agreement {n : ℕ} (d r R k : ℕ) (A : Circ (Fin n))
    (f : MvPolynomial (Fin n) (ZMod 2))
    (herr : ∀ B ∈ A.subcircuits, mulML f (err d r R k B) = 0) :
    mulML f (approx d r R k A) = mulML f (arith A) := by
  apply multilinear_ext_bool (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply,eval_ml,map_mul,arith]
  by_cases hf : eval (toF2 x) f = 0
  · simp [hf]
  have he : eval (toF2 x) (approx d r R k A) = eval (toF2 x) (arithRaw A) := by
    apply eval_agreement d r R k x A
    intro B hB
    have hb := congrArg (eval (toF2 x)) (herr B hB)
    simp only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply,eval_ml,map_mul,map_zero] at hb
    exact (mul_eq_zero.mp hb).resolve_left hf
  rw [he]

end SemAC02.CircuitApproximants
end

section
-- Inlined Solutions.FiniteKernelIntersection

open Module

namespace ProofComplexity.FiniteKernelIntersection

theorem dimension_bound {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (B : Submodule K M) [Module.Finite K B]
    (E : Finset ι) (f : ι → M →ₗ[K] N) :
    finrank K B ≤ finrank K (B ⊓ ⨅ e ∈ E, (f e).ker : Submodule K M) + ∑ e ∈ E, finrank K (B.map (f e)) := by
  classical
  let L := LinearMap.pi (fun e : E => ((f e.1).domRestrict B).rangeRestrict)
  have hker : L.ker.map B.subtype = B ⊓ ⨅ e ∈ E, (f e).ker := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      refine ⟨b.2,?_⟩
      apply (Submodule.mem_iInf (fun e => ⨅ _ : e ∈ E, (f e).ker)).mpr
      intro e
      apply (Submodule.mem_iInf (fun _ : e ∈ E => (f e).ker)).mpr
      intro he
      have hzero : L b = 0 := hb
      have hezero := congrFun hzero (⟨e,he⟩ : E)
      exact congrArg Subtype.val hezero
    · rintro ⟨hxB,hxE⟩
      refine ⟨⟨x,hxB⟩,?_,rfl⟩
      change L ⟨x,hxB⟩ = 0
      funext e
      apply Subtype.ext
      change f e.1 x = 0
      have hx1 := (Submodule.mem_iInf (fun e => ⨅ _ : e ∈ E, (f e).ker)).mp hxE e.1
      exact (Submodule.mem_iInf (fun _ : e.1 ∈ E => (f e.1).ker)).mp hx1 e.2
  have hdimker : finrank K L.ker = finrank K (B ⊓ ⨅ e ∈ E, (f e).ker : Submodule K M) := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  have hdimtarget : finrank K ((e : E) → LinearMap.range ((f e.1).domRestrict B)) =
      ∑ e ∈ E, finrank K (B.map (f e)) := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ e : E, finrank K ((f e.1).domRestrict B).range) = ∑ e : E, finrank K (B.map (f e.1)) := by
        apply Finset.sum_congr rfl
        intro e _
        exact congrArg (fun S : Submodule K N => finrank K S) (LinearMap.range_domRestrict B (f e.1))
      _ = ∑ e ∈ E, finrank K (B.map (f e)) := Finset.sum_coe_sort E (fun e => finrank K (B.map (f e)))
  have hnull := L.finrank_range_add_finrank_ker
  have hrange : finrank K L.range ≤ finrank K ((e : E) → LinearMap.range ((f e.1).domRestrict B)) :=
    Submodule.finrank_le _
  rw [hdimtarget] at hrange
  rw [hdimker] at hnull
  omega

end ProofComplexity.FiniteKernelIntersection
end

section
-- Inlined Solutions.CommonAnnihilator
namespace SemAC02.CommonAnnihilator

open Classical in
/-- **Lemma 4.13 (AC0[2]-Frege approximation with a common annihilator)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission),
Lemma 4.13, p.34): let `d ≥ 2`, and let `F` be a family of AC0[2] circuits of depth at most `d`.
Let `Γ` be the set of distinct rooted subcircuits of circuits in `F`. Choose integers
`r, R ≥ 1`, and set `q = R r^{d−1}` and `α_j = H_n(k − r^{j−1})/(2H_n(k))` for each `j ∈ [d]`.
Assume `r^{d−1} ≤ k ≤ n`. There exist polynomial approximations `p_A` for each `A ∈ Γ` and a
family `Err` of at most `|Γ|` approximation error polynomials with the following properties.

* The degree of `p_A` is at most `r^j` when `A` has depth `j < d`, and it is at most `q` when
  the depth of `A` is exactly `d`.
* Let `𝒜 = {f ∈ B_n^{≤k} : f err = 0 for every err ∈ Err}`. Then
  `λ := dim(𝒜) ≥ (1 − δ) H_n(k)` (7), where `δ = |Γ| exp(−min{r α_{d−1}, R α_d})`.
* Every `f ∈ 𝒜` satisfies `f p_A = f⟦A⟧` for every `A ∈ Γ`.

**Formalization Note** `Γ = F.biUnion subcircuits` (distinct subterms). Products are in `B_n`
(`mulML`); degree of `p_A` is the total degree of a representative. `α_{d−1}` uses
`r^{(d−1)−1} = r^{d−2}`. All subtractions `k − r^{j−1}` are exact since `r^{j−1} ≤ r^{d−1} ≤ k`. -/
theorem common_annihilator {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (F : Finset (Circ (Fin n)))
    (hF : ∀ A ∈ F, A.depth ≤ d) (r R k : ℕ) (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k)
    (hkn : k ≤ n) :
    ∃ (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2))
      (Err : Finset (MvPolynomial (Fin n) (ZMod 2))),
      Err.card ≤ (F.biUnion Circ.subcircuits).card ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth < d → (p A).totalDegree ≤ r ^ A.depth) ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth = d → (p A).totalDegree ≤ R * r ^ (d - 1)) ∧
      (1 - ((F.biUnion Circ.subcircuits).card : ℝ) *
          Real.exp (-(min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
            ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))))) * (Hn n k : ℝ) ≤
        (Module.finrank (ZMod 2)
          (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
            Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : ℝ) ∧
      ∀ f ∈ (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
          Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))),
        ∀ A ∈ F.biUnion Circ.subcircuits, mulML f (p A) = mulML f (arith A)  := by
  classical
  let Γ := F.biUnion Circ.subcircuits
  let p := CircuitApproximants.approx (n := n) d r R k
  let Err := Γ.image (CircuitApproximants.err d r R k)
  have hΓdepth : ∀ A ∈ Γ, A.depth ≤ d := by
    intro A hA
    obtain ⟨B,hB,hAB⟩ := Finset.mem_biUnion.mp hA
    exact (CircuitSubcircuits.properties B A hAB).1.trans (hF B hB)
  have hΓclosed : ∀ A ∈ Γ, A.subcircuits ⊆ Γ := by
    intro A hA B hBA
    obtain ⟨C,hC,hAC⟩ := Finset.mem_biUnion.mp hA
    exact Finset.mem_biUnion.mpr ⟨C,hC,(CircuitSubcircuits.properties C A hAC).2 hBA⟩
  have hErr : Err.card ≤ Γ.card := Finset.card_image_le
  refine ⟨p,Err,hErr,?_,?_,?_,?_⟩
  · intro A hA hdepth
    have hp := CircuitApproximants.approx_degree d r R k hd hr hR hrk hkn A (hΓdepth A hA)
    simpa only [if_neg (ne_of_lt hdepth)] using hp
  · intro A hA hdepth
    have hp := CircuitApproximants.approx_degree d r R k hd hr hR hrk hkn A (hΓdepth A hA)
    simpa only [if_pos hdepth] using hp
  · let θ := CircuitApproximants.theta n d r R k
    let A : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) :=
      Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e)
    let C : ℝ := (Hn n k : ℝ)*Real.exp (-θ)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hdim := ProofComplexity.FiniteKernelIntersection.dimension_bound (Ble (Fin n) k) Err (fun e => mulML e)
    rw [BooleanDimension.finrank_Ble] at hdim
    have hdimR : (Hn n k : ℝ) ≤ (Module.finrank (ZMod 2) A : ℝ)+
        ∑ e ∈ Err, (Module.finrank (ZMod 2) (multSpace e k) : ℝ) := by
      exact_mod_cast hdim
    have hsum : (∑ e ∈ Err, (Module.finrank (ZMod 2) (multSpace e k) : ℝ)) ≤ (Γ.card : ℝ)*C := by
      calc
        _ ≤ ∑ _e ∈ Err, C := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp he
          exact CircuitApproximants.err_rank d r R k hd hr hR hrk hkn B (hΓdepth B hB)
        _ = (Err.card : ℝ)*C := by simp
        _ ≤ (Γ.card : ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hErr) hC
    change (1-(Γ.card : ℝ)*Real.exp (-θ))*(Hn n k : ℝ) ≤ (Module.finrank (ZMod 2) A : ℝ)
    dsimp [C] at hsum
    nlinarith
  · intro f hf A hA
    apply CircuitApproximants.multiplied_agreement d r R k A f
    intro B hB
    have hBΓ := hΓclosed A hA hB
    have he : CircuitApproximants.err d r R k B ∈ Err := Finset.mem_image.mpr ⟨B,hBΓ,rfl⟩
    have hz := (Submodule.mem_iInf (fun e => ⨅ _ : e ∈ Err, LinearMap.ker (mulML e))).mp hf.2
      (CircuitApproximants.err d r R k B)
    have hz' := (Submodule.mem_iInf (fun _ : CircuitApproximants.err d r R k B ∈ Err =>
      LinearMap.ker (mulML (CircuitApproximants.err d r R k B)))).mp hz he
    change mulML f (CircuitApproximants.err d r R k B) = 0
    change mulML (CircuitApproximants.err d r R k B) f = 0 at hz'
    simpa only [mulML,LinearMap.comp_apply,LinearMap.mulLeft_apply,mul_comm] using hz'


end SemAC02.CommonAnnihilator
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_4_13_common_annihilator
open SemAC02

open Classical in
/-- **Lemma 4.13 (AC0[2]-Frege approximation with a common annihilator)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission),
Lemma 4.13, p.34): let `d ≥ 2`, and let `F` be a family of AC0[2] circuits of depth at most `d`.
Let `Γ` be the set of distinct rooted subcircuits of circuits in `F`. Choose integers
`r, R ≥ 1`, and set `q = R r^{d−1}` and `α_j = H_n(k − r^{j−1})/(2H_n(k))` for each `j ∈ [d]`.
Assume `r^{d−1} ≤ k ≤ n`. There exist polynomial approximations `p_A` for each `A ∈ Γ` and a
family `Err` of at most `|Γ|` approximation error polynomials with the following properties.

* The degree of `p_A` is at most `r^j` when `A` has depth `j < d`, and it is at most `q` when
  the depth of `A` is exactly `d`.
* Let `𝒜 = {f ∈ B_n^{≤k} : f err = 0 for every err ∈ Err}`. Then
  `λ := dim(𝒜) ≥ (1 − δ) H_n(k)` (7), where `δ = |Γ| exp(−min{r α_{d−1}, R α_d})`.
* Every `f ∈ 𝒜` satisfies `f p_A = f⟦A⟧` for every `A ∈ Γ`.

**Formalization Note** `Γ = F.biUnion subcircuits` (distinct subterms). Products are in `B_n`
(`mulML`); degree of `p_A` is the total degree of a representative. `α_{d−1}` uses
`r^{(d−1)−1} = r^{d−2}`. All subtractions `k − r^{j−1}` are exact since `r^{j−1} ≤ r^{d−1} ≤ k`. -/
theorem SemAC02.lemma_4_13_common_annihilator {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (F : Finset (Circ (Fin n)))
    (hF : ∀ A ∈ F, A.depth ≤ d) (r R k : ℕ) (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k)
    (hkn : k ≤ n) :
    ∃ (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2))
      (Err : Finset (MvPolynomial (Fin n) (ZMod 2))),
      Err.card ≤ (F.biUnion Circ.subcircuits).card ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth < d → (p A).totalDegree ≤ r ^ A.depth) ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth = d → (p A).totalDegree ≤ R * r ^ (d - 1)) ∧
      (1 - ((F.biUnion Circ.subcircuits).card : ℝ) *
          Real.exp (-(min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
            ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))))) * (Hn n k : ℝ) ≤
        (Module.finrank (ZMod 2)
          (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
            Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : ℝ) ∧
      ∀ f ∈ (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
          Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))),
        ∀ A ∈ F.biUnion Circ.subcircuits, mulML f (p A) = mulML f (arith A) := by
  exact CommonAnnihilator.common_annihilator d hd F hF r R k hr hR hrk hkn


end

section
-- Inlined Solutions.MultipliedSemanticStep

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open SemAC02.BooleanFunctionPolynomials SemAC02.CircuitSemantics SemAC02.RelativeSpaceAlgebra

namespace SemAC02.MultipliedSemanticStep

theorem agreement_on_support {n : ℕ} (f p : MvPolynomial (Fin n) (ZMod 2)) (A : Circ (Fin n))
    (h : mulML f p = mulML f (arith A)) (x : Fin n → Bool)
    (hf : eval (toF2 x) f ≠ 0) : eval (toF2 x) p = if A.eval x then 0 else 1 := by
  have he := congrArg (eval (toF2 x)) h
  simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, eval_ml, map_mul, arith_eval] at he
  exact mul_left_cancel₀ hf he

theorem multiplied_identity {n : ℕ} (f p1 p2 p : MvPolynomial (Fin n) (ZMod 2))
    (hsem : ∀ x : Fin n → ZMod 2, eval x f ≠ 0 → eval x p1 = 0 → eval x p2 = 0 → eval x p = 0) :
    mulML f p = ML (mulML f p1 * (p * (1+p2)) + mulML f p2 * p) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, eval_ml, map_mul, map_add, map_one]
  by_cases hf : eval x f = 0
  · simp [hf]
  rcases AC02Frege.MajorityFoundation.eq_zero_or_one (eval x p1) with h1 | h1 <;>
    rcases AC02Frege.MajorityFoundation.eq_zero_or_one (eval x p2) with h2 | h2
  · rw [hsem x hf h1 h2, h1, h2]
    simp
  all_goals simp [h1,h2,CharTwo.add_self_eq_zero]

theorem relative_semantic_step {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (q : ℕ)
    (f p1 p2 p : MvPolynomial (Fin n) (ZMod 2))
    (hp1 : RelativePC.Derivable P (multSpace f (3*q)) (mulML f p1))
    (hp2 : RelativePC.Derivable P (multSpace f (3*q)) (mulML f p2))
    (hd1 : p1.totalDegree ≤ q) (hd2 : p2.totalDegree ≤ q) (hd : p.totalDegree ≤ q)
    (hsem : ∀ x : Fin n → ZMod 2, eval x f ≠ 0 → eval x p1 = 0 → eval x p2 = 0 → eval x p = 0) :
    RelativePC.Derivable P (multSpace f (3*q)) (mulML f p) := by
  rw [multiplied_identity f p1 p2 p hsem, map_add]
  apply RelativePC.pc_add
  · apply relative_polynomial_mul P f p1 (p*(1+p2)) (3*q) hp1
    have hplus : (1+p2).totalDegree ≤ q := (totalDegree_add _ _).trans (by simpa using hd2)
    have hprod := totalDegree_mul p (1+p2)
    omega
  · apply relative_polynomial_mul P f p2 p (3*q) hp2
    omega

theorem consequence_on_support {n : ℕ} (f p1 p2 p : MvPolynomial (Fin n) (ZMod 2))
    (A1 A2 A : Circ (Fin n))
    (h1 : mulML f p1 = mulML f (arith A1))
    (h2 : mulML f p2 = mulML f (arith A2))
    (h : mulML f p = mulML f (arith A))
    (hsem : ∀ x : Fin n → Bool, A1.eval x = true → A2.eval x = true → A.eval x = true) :
    ∀ x : Fin n → ZMod 2, eval x f ≠ 0 → eval x p1 = 0 → eval x p2 = 0 → eval x p = 0 := by
  intro x hfx hx1 hx2
  obtain ⟨X,rfl⟩ := toF2_surjective x
  have he1 := agreement_on_support f p1 A1 h1 X hfx
  have he2 := agreement_on_support f p2 A2 h2 X hfx
  have he := agreement_on_support f p A h X hfx
  have hA1 : A1.eval X = true := by
    cases ha : A1.eval X <;> simp_all
  have hA2 : A2.eval X = true := by
    cases ha : A2.eval X <;> simp_all
  simpa only [hsem X hA1 hA2, ↓reduceIte] using he

end SemAC02.MultipliedSemanticStep
end

section
-- Inlined Solutions.SemanticRefutationSoundness

namespace SemAC02.RefutationSoundness

theorem false_mem {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ) (π : List (Circ (Fin n)))
    (hπ : IsSemRefutation d F π) : Circ.const false ∈ π := by
  obtain ⟨ρ,hρ⟩ := List.getLast?_eq_some_iff.mp hπ.2.2
  rw [hρ]
  simp

theorem unsatisfiable {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ) (π : List (Circ (Fin n)))
    (hπ : IsSemRefutation d F π) (x : Fin n → Bool) : ¬ ∀ A ∈ F, A.eval x = true := by
  intro hx
  have hall : ∀ k (hk : k < π.length), π[k].eval x = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ.2.1 k hk with ha | ha | ⟨i,j,hi,hj,hsem⟩
      · exact hx _ ha
      · exact ha x
      · exact hsem x (ih i hi (hi.trans hk)) (ih j hj (hj.trans hk))
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (false_mem F d π hπ)
  have h := hall i hi
  rw [he] at h
  exact Bool.false_ne_true (by simpa only [Circ.eval] using h)

theorem axioms_nonempty {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ) (π : List (Circ (Fin n)))
    (hπ : IsSemRefutation d F π) : F.Nonempty := by
  classical
  by_contra! h
  apply unsatisfiable F d π hπ (fun _ => false)
  intro A hA
  simpa only [h, Set.mem_empty_iff_false] using hA

end SemAC02.RefutationSoundness
end

section
-- Inlined Solutions.SemanticSimulationAfterMultiplication

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.BooleanFunctionPolynomials SemAC02.CircuitSemantics SemAC02.RelativeSpaceAlgebra
open SemAC02.MultipliedSemanticStep

namespace SemAC02.SimulationAfterMultiplication

theorem tautology_product_zero {n : ℕ} (f p : MvPolynomial (Fin n) (ZMod 2))
    (A : Circ (Fin n)) (h : mulML f p = mulML f (arith A))
    (hA : ∀ x : Fin n → Bool, A.eval x = true) : mulML f p = 0 := by
  rw [h]
  apply multilinear_ext_bool (ml_multilinear _) ((mem_restrictDegree _ _ 1).mp (Submodule.zero_mem _))
  intro x
  simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, eval_ml, map_mul, arith_eval,
    hA x, ↓reduceIte, mul_zero, map_zero]

theorem relative_simulation {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ)
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) (q : ℕ)
    (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2)) (hp : ∀ A ∈ π, (p A).totalDegree ≤ q)
    (f : MvPolynomial (Fin n) (ZMod 2)) (hfml : IsMultilinear f)
    (hfp : ∀ A ∈ π, mulML f (p A) = mulML f (arith A)) :
    RelativePC.Derivable (mulML f '' (arith '' F)) (multSpace f (3*q)) f := by
  classical
  let P := mulML f '' (arith '' F)
  have hall : ∀ k (hk : k < π.length),
      RelativePC.Derivable P (multSpace f (3*q)) (mulML f (p π[k])) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hmem : π[k] ∈ π := List.getElem_mem hk
      rcases hπ.2.1 k hk with hA | hA | ⟨i,j,hi,hj,hsem⟩
      · have hpP : mulML f (p π[k]) ∈ P := by
          rw [hfp _ hmem]
          exact ⟨arith π[k], ⟨π[k],hA,rfl⟩,rfl⟩
        have hml := ml_of_multilinear (mulML f (p π[k])) (ml_multilinear _)
        rw [← hml]
        apply RelativePC.pc_axiom P (multSpace f (3*q)) _ hpP
        rw [hml]
        exact mem_multSpace_of_degree f (p π[k]) (3*q) (by have := hp _ hmem; omega)
      · rw [tautology_product_zero f (p π[k]) π[k] (hfp _ hmem) hA]
        exact RelativePC.pc_zero P _
      · apply relative_semantic_step P q f (p π[i]) (p π[j]) (p π[k])
          (ih i hi (hi.trans hk)) (ih j hj (hj.trans hk))
          (hp _ (List.getElem_mem (hi.trans hk))) (hp _ (List.getElem_mem (hj.trans hk))) (hp _ hmem)
        exact consequence_on_support f _ _ _ π[i] π[j] π[k]
          (hfp _ (List.getElem_mem (hi.trans hk))) (hfp _ (List.getElem_mem (hj.trans hk))) (hfp _ hmem) hsem
  have hlast := RefutationSoundness.false_mem F d π hπ
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hlast
  have hout := hall i hi
  rw [he, hfp _ hlast] at hout
  have hfalse : mulML f (arith (Circ.const false)) = f := by
    apply multilinear_ext_bool (ml_multilinear _) hfml
    intro x
    simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, eval_ml, map_mul,
      arith_eval, Circ.eval, Bool.false_eq_true, ↓reduceIte, mul_one]
  rwa [hfalse] at hout

theorem simulation {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ)
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) (q k : ℕ)
    (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2)) (hp : ∀ A ∈ π, (p A).totalDegree ≤ q)
    (f : MvPolynomial (Fin n) (ZMod 2)) (hf : f ∈ Ble (Fin n) k)
    (hfp : ∀ A ∈ π, mulML f (p A) = mulML f (arith A)) :
    ∃ τ : List (MvPolynomial (Fin n) (ZMod 2)),
      PCNonBool.IsDerivation ML (mulML f '' (arith '' F)) τ ∧ f ∈ τ ∧
      (∀ u ∈ τ, ∃ Q : MvPolynomial (Fin n) (ZMod 2), Q.totalDegree ≤ 3*q ∧ u = mulML f Q) ∧
      ∀ u ∈ τ, u.totalDegree ≤ k+3*q := by
  classical
  have hrel := relative_simulation F d π hπ q p hp f ((mem_Ble_iff k f).mp hf).1 hfp
  rcases hrel with hzero | ⟨τ,hτ,hspace,hfτ⟩
  · obtain ⟨A,hA⟩ := RefutationSoundness.axioms_nonempty F d π hπ
    refine ⟨[0], ?_, by simp [hzero], ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst i
      left
      exact ⟨mulML f (arith A), ⟨arith A,⟨A,hA,rfl⟩,rfl⟩,0,by simp⟩
    · intro u hu
      have hu0 : u = 0 := List.mem_singleton.mp hu
      subst u
      refine ⟨0,by simp,?_⟩
      simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_zero, map_zero]
    · intro u hu
      have hu0 : u = 0 := List.mem_singleton.mp hu
      subst u
      simp
  · refine ⟨τ,hτ,hfτ,?_,?_⟩
    · intro u hu
      obtain ⟨Q,hQ,hval⟩ := hspace u hu
      exact ⟨Q,((mem_Ble_iff (3*q) Q).mp hQ).2,hval.symm⟩
    · intro u hu
      exact multSpace_degree f u k (3*q) hf (hspace u hu)

end SemAC02.SimulationAfterMultiplication
end

section
-- Inlined Solutions.RelativePseudoReductionSoundness

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02.RelativeSpaceAlgebra

namespace SemAC02.RelativePseudoReductionSoundness

theorem multiplier_self_mem {n : ℕ} (f : MvPolynomial (Fin n) (ZMod 2))
    (hf : IsMultilinear f) (D : ℕ) : f ∈ multSpace f D := by
  have h := mem_multSpace_of_degree f 1 D (by simp)
  have he : mulML f 1 = f := by
    simp only [mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one]
    exact ml_of_multilinear f hf
  rwa [he] at h

theorem annihilates_derivation {n : ℕ} (S : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : multSpace f D →ₗ[ZMod 2] W) (hR : IsRelPseudoRed S f D R)
    (τ : List (MvPolynomial (Fin n) (ZMod 2)))
    (hτ : PCNonBool.IsDerivation ML (mulML f '' S) τ)
    (hspace : ∀ u ∈ τ, u ∈ multSpace f D) :
    ∀ (u) (hu : u ∈ τ), R ⟨u,hspace u hu⟩ = 0 := by
  classical
  have hmem (i : ℕ) (hi : i < τ.length) := hspace _ (List.getElem_mem hi)
  have hall : ∀ i (hi : i < τ.length), R ⟨τ[i],hmem i hi⟩ = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      rcases hτ i hi with ha | ha | ha
      · obtain ⟨a,ha,c,he⟩ := ha
        obtain ⟨b,hb,rfl⟩ := ha
        have hml : ML (mulML f b) = mulML f b := ml_idempotent _
        rw [hml] at he
        rcases AC02Frege.MajorityFoundation.eq_zero_or_one c with hc | hc
        · have hzero : τ[i] = 0 := by simpa only [hc,zero_smul] using he
          have hsub : (⟨τ[i],hmem i hi⟩ : multSpace f D) = 0 := Subtype.ext hzero
          rw [hsub,map_zero]
        · have heq : τ[i] = mulML f b := by simpa only [hc,one_smul] using he
          have hbmem : mulML f b ∈ multSpace f D := heq ▸ hmem i hi
          have hsub : (⟨τ[i],hmem i hi⟩ : multSpace f D) = ⟨mulML f b,hbmem⟩ := Subtype.ext heq
          rw [hsub]
          exact hR.1 b hb hbmem
      · obtain ⟨j,k,hj,hk,a,b,he⟩ := ha
        have hsub : (⟨τ[i],hmem i hi⟩ : multSpace f D) =
            a • ⟨τ[j],hmem j (hj.trans hi)⟩ + b • ⟨τ[k],hmem k (hk.trans hi)⟩ := Subtype.ext he
        rw [hsub,map_add,map_smul,map_smul,ih j hj (hj.trans hi),ih k hk (hk.trans hi)]
        simp
      · obtain ⟨j,hj,v,he⟩ := ha
        have hprod : ML (X v * τ[j]) ∈ multSpace f D := he ▸ hmem i hi
        have hsub : (⟨τ[i],hmem i hi⟩ : multSpace f D) = ⟨ML (X v * τ[j]),hprod⟩ := Subtype.ext he
        rw [hsub]
        exact hR.2 v ⟨τ[j],hmem j (hj.trans hi)⟩ hprod (ih j hj (hj.trans hi))
  intro u hu
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hu
  subst u
  exact hall i hi

theorem zero_of_self_zero {n : ℕ} (S : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f : MvPolynomial (Fin n) (ZMod 2)) (hf : IsMultilinear f) (D : ℕ)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : multSpace f D →ₗ[ZMod 2] W) (hR : IsRelPseudoRed S f D R)
    (hself : R ⟨f,multiplier_self_mem f hf D⟩ = 0) : R = 0 := by
  classical
  have hkill : ∀ (A : Finset (Fin n)) (hA : A.card ≤ D),
      R ⟨mulML f (xMon A),mem_multSpace_of_degree f (xMon A) D ((xMon_totalDegree A).trans_le hA)⟩ = 0 := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro hA
      have he : mulML f (xMon ∅) = f := by
        simp only [xMon, Finset.prod_empty, mulML, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one]
        exact ml_of_multilinear f hf
      have hsub : (⟨mulML f (xMon ∅),mem_multSpace_of_degree f (xMon ∅) D ((xMon_totalDegree ∅).trans_le hA)⟩ : multSpace f D) =
          ⟨f,multiplier_self_mem f hf D⟩ := Subtype.ext he
      simpa only [hsub] using hself
    | @insert v A hv ih =>
      intro hA
      have hAc : A.card ≤ D := (Finset.card_le_card (Finset.subset_insert v A)).trans hA
      let u : multSpace f D := ⟨mulML f (xMon A),mem_multSpace_of_degree f (xMon A) D
        ((xMon_totalDegree A).trans_le hAc)⟩
      have he : ML (X v * (u : MvPolynomial (Fin n) (ZMod 2))) = mulML f (xMon (insert v A)) := by
        change ML (X v * ML (f*xMon A)) = ML (f*xMon (insert v A))
        rw [ml_mul_right]
        simp only [xMon, Finset.prod_insert hv]
        congr 1
        ring
      have hprod : ML (X v * (u : MvPolynomial (Fin n) (ZMod 2))) ∈ multSpace f D := by
        rw [he]
        exact mem_multSpace_of_degree f (xMon (insert v A)) D ((xMon_totalDegree _).trans_le hA)
      have hzero := hR.2 v u hprod (ih hAc)
      have hsub : (⟨ML (X v * (u : MvPolynomial (Fin n) (ZMod 2))),hprod⟩ : multSpace f D) =
          ⟨mulML f (xMon (insert v A)),mem_multSpace_of_degree f (xMon (insert v A)) D ((xMon_totalDegree _).trans_le hA)⟩ := Subtype.ext he
      rwa [hsub] at hzero
  let N := R.ker.map (multSpace f D).subtype
  have hle : Ble (Fin n) D ≤ N.comap (mulML f) := by
    apply Submodule.span_le.mpr
    rintro p ⟨A,hA,rfl⟩
    exact ⟨⟨mulML f (xMon A),mem_multSpace_of_degree f (xMon A) D ((xMon_totalDegree A).trans_le hA)⟩,
      hkill A hA,rfl⟩
  apply LinearMap.ext
  intro u
  obtain ⟨q,hq,heq⟩ := u.2
  obtain ⟨u',hu',he⟩ := hle hq
  have hsub : u' = u := Subtype.ext (he.trans heq)
  rw [hsub] at hu'
  exact hu'

theorem no_derivation_of_nonzero {n : ℕ} (S : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f : MvPolynomial (Fin n) (ZMod 2)) (hf : IsMultilinear f) (D : ℕ)
    (hred : HasNonzeroRelPseudoRed S f D)
    (τ : List (MvPolynomial (Fin n) (ZMod 2)))
    (hτ : PCNonBool.IsDerivation ML (mulML f '' S) τ)
    (hspace : ∀ u ∈ τ, u ∈ multSpace f D) (hfτ : f ∈ τ) : False := by
  obtain ⟨W,hW,mW,R,hne,hR⟩ := hred
  letI := hW
  letI := mW
  apply hne
  apply zero_of_self_zero S f hf D R hR
  exact annihilates_derivation S f D R hR τ hτ hspace f hfτ

end SemAC02.RelativePseudoReductionSoundness
end

section
-- Inlined Solutions.SemanticSizeBound

open Module MvPolynomial AC02Frege
open SemAC02.RelativeSpaceAlgebra SemAC02.BooleanDimension

namespace SemAC02.SizeBound

theorem self_mem_subcircuits {V : Type} (A : Circ V) : A ∈ A.subcircuits := by
  cases A <;> simp only [Circ.subcircuits, Finset.mem_insert, Finset.mem_singleton, true_or]

theorem size_bound {n : ℕ} (F : Set (Circ (Fin n))) (d r R k : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k) (hkn : k ≤ n)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hU : U ≤ Ble (Fin n) k)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n k : ℝ) *
        Real.exp (min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
          ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))) ≤
      (proofSize π : ℝ) := by
  classical
  let θ : ℝ := min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
    ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))
  let Γ := π.toFinset.biUnion Circ.subcircuits
  obtain ⟨p,Err,hcard,hplow,hptop,hdim,hfp⟩ := lemma_4_13_common_annihilator d hd π.toFinset
    (fun A hA => hπ.1 A (List.mem_toFinset.mp hA)) r R k hr hR hrk hkn
  let A : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) :=
    Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e)
  have hA : A ≤ Ble (Fin n) k := inf_le_left
  have hline (B : Circ (Fin n)) (hB : B ∈ π) : B ∈ Γ :=
    Finset.mem_biUnion.mpr ⟨B,List.mem_toFinset.mpr hB,self_mem_subcircuits B⟩
  have hp : ∀ B ∈ π, (p B).totalDegree ≤ R * r ^ (d-1) := by
    intro B hB
    have hdepth := hπ.1 B hB
    rcases lt_or_eq_of_le hdepth with hlt | heq
    · have hsmall := hplow B (hline B hB) hlt
      have hpow : r ^ B.depth ≤ r ^ (d-1) := Nat.pow_le_pow_right hr (by omega)
      have hmul : r ^ (d-1) ≤ R * r ^ (d-1) := by nlinarith
      exact hsmall.trans (hpow.trans hmul)
    · exact hptop B (hline B hB) heq
  have hinter : U ⊓ A = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    by_contra hne
    obtain ⟨τ,hτ,hfτ,hquot,hdeg⟩ := SimulationAfterMultiplication.simulation F d π hπ
      (R*r^(d-1)) k p hp f (hU hf.1) (fun B hB => hfp f hf.2 B (hline B hB))
    apply RelativePseudoReductionSoundness.no_derivation_of_nonzero (arith '' F) f
      ((mem_Ble_iff k f).mp (hU hf.1)).1 (3*(R*r^(d-1))) (hred f hf.1 hne) τ hτ
    · intro u hu
      obtain ⟨Q,hQ,rfl⟩ := hquot u hu
      exact mem_multSpace_of_degree f Q _ hQ
    · exact hfτ
  letI : Module.Finite (ZMod 2) U := Submodule.finiteDimensional_of_le hU
  letI : Module.Finite (ZMod 2) A := Submodule.finiteDimensional_of_le hA
  have hsum : finrank (ZMod 2) U + finrank (ZMod 2) A ≤ Hn n k := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq U A
    rw [hinter,finrank_bot,add_zero] at he
    rw [← he, ← finrank_Ble n k]
    exact Submodule.finrank_mono (sup_le hU hA)
  have hsumR : (finrank (ZMod 2) U : ℝ) + (finrank (ZMod 2) A : ℝ) ≤ (Hn n k : ℝ) := by exact_mod_cast hsum
  have hdimR : (1 - (Γ.card : ℝ) * Real.exp (-θ)) * (Hn n k : ℝ) ≤
      (finrank (ZMod 2) A : ℝ) := hdim
  have hbound : (finrank (ZMod 2) U : ℝ) ≤ (Γ.card : ℝ) * Real.exp (-θ) * (Hn n k : ℝ) := by
    nlinarith
  have hH : (0 : ℝ) < (Hn n k : ℝ) := by exact_mod_cast Hn_pos n k
  have hdiv : (finrank (ZMod 2) U : ℝ) / (Hn n k : ℝ) ≤ (Γ.card : ℝ) * Real.exp (-θ) :=
    (div_le_iff₀ hH).mpr hbound
  have hmul := mul_le_mul_of_nonneg_right hdiv (Real.exp_pos θ).le
  have hexp : Real.exp (-θ) * Real.exp θ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [mul_assoc,hexp,mul_one] at hmul
  exact hmul

end SemAC02.SizeBound
end

section
-- Inlined Theorems.Thm_SemAC02_theorem_4_16_size_bound
open SemAC02

/-- **Theorem 4.16 (Size bound via relative pseudo-reduction operators)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission),
Theorem 4.16, p.36): let `F` be a family of circuits in `n` variables, and put
`S = {⟦A⟧ : A ∈ F}`. Fix `d ≥ 2`, integers `r, R ≥ 1` and `r^{d−1} ≤ k ≤ n`, and put
`q = R r^{d−1}`, `α_j = H_n(k − r^{j−1})/(2H_n(k))`, `θ = min{r α_{d−1}, R α_d}`. Suppose
`U ⊆ B_n^{≤k}` is a linear subspace such that, for every `0 ≠ f ∈ U`, there is a non-zero
`f`-relative pseudo-reduction of degree `3q` for `S`. Then every depth-`d` semantic
AC0[2]-Frege refutation `π` of `F` satisfies `size(π) ≥ (dim(U)/H_n(k)) exp(θ)` (10).

**Formalization Note** `dim` is `Module.finrank`; the pseudo-reduction may take values in any
`𝔽₂`-vector space `W : Type` (`HasNonzeroRelPseudoRed`). `size(π)` is `proofSize π`. -/
theorem SemAC02.theorem_4_16_size_bound {n : ℕ} (F : Set (Circ (Fin n))) (d r R k : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k) (hkn : k ≤ n)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hU : U ≤ Ble (Fin n) k)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n k : ℝ) *
        Real.exp (min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
          ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))) ≤
      (proofSize π : ℝ) := by
  exact SizeBound.size_bound F d r R k hd hr hR hrk hkn U hU hred π hπ


end

section
-- Inlined Solutions.NearHalfBinomialStep

set_option maxHeartbeats 1000000

namespace SemAC02.NearHalfBinomialStep

theorem parameter_buffer {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) : 2+1/(32*ε) ≤ ε*n/2 := by
  have hb : 16 ≤ (n : ℝ)*ε^2 := (div_le_iff₀ (sq_pos_of_pos hε₀)).mp hn
  have he : ε*(1/(32*ε)) = (1/32 : ℝ) := by field_simp
  apply (mul_le_mul_iff_of_pos_right hε₀).mp
  nlinarith

theorem cutoff_le_n {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256) :
    ⌊(1/2-ε)*(n : ℝ)⌋₊ ≤ n := by
  have harg : 0 ≤ (1/2-ε)*(n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hfl := Nat.floor_le harg
  have he : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ) ≤ n := by nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact_mod_cast he

theorem window_lower {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j s : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hs : s ≤ ⌊1/(32*ε)⌋₊) :
    (1/2-2*ε)*(n : ℝ)+1 ≤ (j : ℝ)-(s : ℝ) := by
  have hfl := Nat.lt_floor_add_one ((1/2-ε)*(n : ℝ))
  have hs' : (s : ℝ) ≤ 1/(32*ε) :=
    (Nat.cast_le.mpr hs).trans (Nat.floor_le (by positivity))
  have hb := parameter_buffer hε₀ hε hn
  nlinarith

/-- The consecutive-binomial comparison in the short window used by source Lemma 4.17. -/
theorem binomial_step {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j s : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hjk : j ≤ ⌊(1/2-ε)*(n : ℝ)⌋₊) (hs : s ≤ ⌊1/(32*ε)⌋₊) :
    (1-8*ε)*(n.choose (j-s) : ℝ) ≤ n.choose (j-s-1) := by
  have hlo := window_lower hε₀ hε hn j s hj hs
  have hco : 0 ≤ (1/2-2*ε)*(n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hs_le : s ≤ j := by exact_mod_cast (by linarith : (s : ℝ) ≤ j)
  have hmpos : 1 ≤ j-s := by
    have he : (1 : ℝ) ≤ ((j-s : ℕ) : ℝ) := by rw [Nat.cast_sub hs_le]; linarith
    exact_mod_cast he
  have hmn : j-s ≤ n := (Nat.sub_le j s).trans (hjk.trans (cutoff_le_n hε₀ hε))
  have hrec0 := Nat.choose_succ_right_eq n (j-s-1)
  rw [Nat.sub_add_cancel hmpos] at hrec0
  have hsub : n-(j-s-1) = n-(j-s)+1 := by omega
  rw [hsub] at hrec0
  have hrec : (n.choose (j-s) : ℝ)*((j-s : ℕ) : ℝ) =
      (n.choose (j-s-1) : ℝ)*(((n-(j-s)+1 : ℕ)) : ℝ) := by exact_mod_cast hrec0
  have hDpos : (0 : ℝ) < (((n-(j-s)+1 : ℕ)) : ℝ) := by positivity
  have hD : (((n-(j-s)+1 : ℕ)) : ℝ) ≤ (1/2+2*ε)*(n : ℝ) := by
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub hmn,Nat.cast_sub hs_le]
    linarith
  have hcoef : (1-8*ε)*((1/2+2*ε)*(n : ℝ)) ≤ (1/2-2*ε)*(n : ℝ) := by
    nlinarith [mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg n)]
  have hratio : (1-8*ε)*((((n-(j-s)+1 : ℕ)) : ℝ)) ≤ ((j-s : ℕ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 1-8*ε)
    rw [Nat.cast_sub hs_le]
    linarith
  apply (mul_le_mul_iff_of_pos_right hDpos).mp
  calc
    _ = (n.choose (j-s) : ℝ)*((1-8*ε)*((((n-(j-s)+1 : ℕ)) : ℝ))) := by ring
    _ ≤ (n.choose (j-s) : ℝ)*((j-s : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
    _ = _ := hrec

end SemAC02.NearHalfBinomialStep
end

section
-- Inlined Solutions.NearHalfCumulativeCounts

set_option maxHeartbeats 1000000

open Finset
open SemAC02.NearHalfBinomialStep

namespace SemAC02.NearHalfCumulativeCounts

theorem binomial_power_window {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j s : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hjk : j ≤ ⌊(1/2-ε)*(n : ℝ)⌋₊) (hs : s ≤ ⌊1/(32*ε)⌋₊) :
    (1-8*ε)^s*(n.choose j : ℝ) ≤ n.choose (j-s) := by
  revert hs
  induction s with
  | zero => intro _; simp only [pow_zero,one_mul,Nat.sub_zero,le_refl]
  | succ s ih =>
    intro hs
    have hp := ih (by omega)
    have he := binomial_step hε₀ hε hn j s hj hjk (by omega)
    calc
      _ = (1-8*ε)*((1-8*ε)^s*(n.choose j : ℝ)) := by rw [pow_succ]; ring
      _ ≤ (1-8*ε)*(n.choose (j-s) : ℝ) := mul_le_mul_of_nonneg_left hp (by linarith)
      _ ≤ _ := by simpa only [Nat.sub_sub] using he

theorem binomial_window_lower {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j s : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hjk : j ≤ ⌊(1/2-ε)*(n : ℝ)⌋₊) (hs : s ≤ ⌊1/(32*ε)⌋₊) :
    (3/4 : ℝ)*(n.choose j : ℝ) ≤ n.choose (j-s) := by
  have hs' : (s : ℝ) ≤ 1/(32*ε) := (Nat.cast_le.mpr hs).trans (Nat.floor_le (by positivity))
  have he : ε*(1/(32*ε)) = (1/32 : ℝ) := by field_simp
  have hprod : 8*ε*(s : ℝ) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hs' hε₀.le]
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -8*ε by linarith) s
  have hpow : (3/4 : ℝ) ≤ (1-8*ε)^s := by
    rw [show (1 : ℝ)+(-8*ε) = 1-8*ε by ring] at hb
    nlinarith
  exact (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)).trans
    (binomial_power_window hε₀ hε hn j s hj hjk hs)

/-- The last binomial layer occupies at most a 64ε fraction of the cumulative count. -/
theorem layer_fraction_bound {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hjk : j ≤ ⌊(1/2-ε)*(n : ℝ)⌋₊) :
    (n.choose j : ℝ) ≤ 64*ε*(Hn n j : ℝ) := by
  let t := ⌊1/(32*ε)⌋₊
  have hlo := window_lower hε₀ hε hn j t hj le_rfl
  have hco : 0 ≤ (1/2-2*ε)*(n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have htj : t ≤ j := by exact_mod_cast (by linarith : (t : ℝ) ≤ j)
  have hinj : Set.InjOn (fun s : ℕ => j-s) (range (t+1)) := by
    intro s hs s' hs' he
    have hsle := mem_range.mp hs
    have hsle' := mem_range.mp hs'
    change j-s = j-s' at he
    omega
  let E := (range (t+1)).image (fun s => j-s)
  have hE : E ⊆ range (j+1) := by
    intro i hi
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (by omega)
  have hsum : (∑ s ∈ range (t+1), (n.choose (j-s) : ℝ)) ≤ (Hn n j : ℝ) := by
    rw [Hn,min_eq_left (hjk.trans (cutoff_le_n hε₀ hε)),Nat.cast_sum]
    have heq : (∑ i ∈ E, (n.choose i : ℝ)) = ∑ s ∈ range (t+1), (n.choose (j-s) : ℝ) := sum_image hinj
    rw [← heq]
    exact sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => Nat.cast_nonneg _)
  have hlow : (((t : ℝ)+1)*(3/4))*(n.choose j : ℝ) ≤ (Hn n j : ℝ) := by
    calc
      _ = ∑ _s ∈ range (t+1), (3/4 : ℝ)*(n.choose j : ℝ) := by simp [mul_assoc]
      _ ≤ ∑ s ∈ range (t+1), (n.choose (j-s) : ℝ) := by
        apply sum_le_sum
        intro s hs
        exact binomial_window_lower hε₀ hε hn j s hj hjk (by have := mem_range.mp hs; omega)
      _ ≤ _ := hsum
  have ht : 1/(32*ε) < (t : ℝ)+1 := Nat.lt_floor_add_one _
  have hcoef : 1 ≤ 64*ε*((t : ℝ)+1)*(3/4) := by
    have he := (div_lt_iff₀ (by positivity : (0 : ℝ) < 32*ε)).mp ht
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 64*ε by positivity)
  have hmul' := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (n.choose j) : (0 : ℝ) ≤ _)
  nlinarith

theorem exp_step_bound {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256) :
    Real.exp (-(128*ε)) ≤ 1-64*ε := by
  have he : 1+128*ε ≤ Real.exp (128*ε) := by linarith [Real.add_one_le_exp (128*ε)]
  have hi := one_div_le_one_div_of_le (show (0 : ℝ) < 1+128*ε by linarith) he
  have hb : 1/(1+128*ε) ≤ 1-64*ε := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1+128*ε)).mpr
    nlinarith [mul_nonneg hε₀.le (show 0 ≤ 1/256-ε by linarith)]
  simpa only [one_div,← Real.exp_neg] using hi.trans hb

theorem cumulative_step {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (j : ℕ)
    (hj : (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ)-ε*n/2 ≤ j)
    (hjk : j ≤ ⌊(1/2-ε)*(n : ℝ)⌋₊) :
    Real.exp (-(128*ε))*(Hn n j : ℝ) ≤ Hn n (j-1) := by
  have hlo := window_lower hε₀ hε hn j 0 hj (Nat.zero_le _)
  have hco : 0 ≤ (1/2-2*ε)*(n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
  have hjpos : 1 ≤ j := by
    have he : (1 : ℝ) ≤ j := by norm_num at hlo; linarith
    exact_mod_cast he
  have hjn := hjk.trans (cutoff_le_n hε₀ hε)
  have hsum : Hn n j = Hn n (j-1)+n.choose j := by
    simp only [Hn,min_eq_left hjn,min_eq_left ((Nat.sub_le j 1).trans hjn),Nat.sub_add_cancel hjpos]
    exact sum_range_succ _ _
  have hl := layer_fraction_bound hε₀ hε hn j hj hjk
  have hs : (Hn n j : ℝ) = (Hn n (j-1) : ℝ)+(n.choose j : ℝ) := by exact_mod_cast hsum
  have hm := mul_le_mul_of_nonneg_right (exp_step_bound hε₀ hε) (Nat.cast_nonneg (Hn n j) : (0 : ℝ) ≤ _)
  nlinarith

end SemAC02.NearHalfCumulativeCounts
end

section
-- Inlined Solutions.NearHalfCumulativeRatio

set_option maxHeartbeats 1000000

open SemAC02.NearHalfBinomialStep SemAC02.NearHalfCumulativeCounts

namespace SemAC02.NearHalfCumulativeRatio

theorem budget_le_cutoff {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) :
    ε*n/2 ≤ (⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ) := by
  let k := ⌊(1/2-ε)*(n : ℝ)⌋₊
  have hj : (k : ℝ)-ε*n/2 ≤ k := by nlinarith [mul_nonneg hε₀.le (Nat.cast_nonneg n)]
  have hlo := window_lower hε₀ hε hn k 0 hj (Nat.zero_le _)
  simp only [Nat.cast_zero,sub_zero] at hlo
  have hc : 0 ≤ (1/2-(5/2)*ε)*(n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
  nlinarith

/-- Lemma 4.17: the cumulative-binomial count changes slowly near half the variables. -/
theorem cumulative_ratio {n : ℕ} {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1/256)
    (hn : 16/ε^2 ≤ (n : ℝ)) (a : ℕ) (ha : (a : ℝ) ≤ ε*n/2) :
    Real.exp (-(128*ε*(a : ℝ))) ≤
      (Hn n (⌊(1/2-ε)*(n : ℝ)⌋₊-a) : ℝ)/(Hn n ⌊(1/2-ε)*(n : ℝ)⌋₊ : ℝ) := by
  let k := ⌊(1/2-ε)*(n : ℝ)⌋₊
  let δ := Real.exp (-(128*ε))
  have hak : a ≤ k := by exact_mod_cast ha.trans (budget_le_cutoff hε₀ hε hn)
  have hiter : ∀ i : ℕ, i ≤ a → δ^i*(Hn n k : ℝ) ≤ Hn n (k-i) := by
    intro i
    induction i with
    | zero => intro _; simp only [pow_zero,one_mul,Nat.sub_zero,le_refl]
    | succ i ih =>
      intro hi
      have hia : i ≤ a := by omega
      have hik := hia.trans hak
      have hj : (k : ℝ)-ε*n/2 ≤ ((k-i : ℕ) : ℝ) := by
        rw [Nat.cast_sub hik]
        have hi' : (i : ℝ) ≤ a := by exact_mod_cast hia
        linarith
      have hs := cumulative_step hε₀ hε hn (k-i) hj (Nat.sub_le k i)
      calc
        _ = δ*(δ^i*(Hn n k : ℝ)) := by rw [pow_succ]; ring
        _ ≤ δ*(Hn n (k-i) : ℝ) := mul_le_mul_of_nonneg_left (ih hia) (Real.exp_nonneg _)
        _ ≤ (Hn n (k-i-1) : ℝ) := hs
        _ = _ := by rw [Nat.sub_sub]
  have he : δ^a = Real.exp (-(128*ε*(a : ℝ))) := by
    dsimp only [δ]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp := hiter a le_rfl
  rw [he] at hp
  exact (le_div_iff₀ (by exact_mod_cast BooleanDimension.Hn_pos n k : (0 : ℝ) < Hn n k)).mpr hp

end SemAC02.NearHalfCumulativeRatio
end

section
-- Inlined Solutions.NumericalSizeBound

set_option maxHeartbeats 1000000

open Module MvPolynomial
open SemAC02.NearHalfBinomialStep SemAC02.NearHalfCumulativeRatio

namespace SemAC02.NumericalSizeBound

theorem corollary_size_bound {n : ℕ} (F : Set (Circ (Fin n))) (d r R : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 256)
    (hn : 16 / ε ^ 2 ≤ (n : ℝ)) (hrn : (r : ℝ) ^ (d - 1) ≤ ε * n / 2)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hU : U ≤ Ble (Fin n) ⌊(1 / 2 - ε) * (n : ℝ)⌋₊)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n ⌊(1 / 2 - ε) * (n : ℝ)⌋₊ : ℝ) *
        Real.exp (1 / 2 * min ((r : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 2))))
          ((R : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 1))))) ≤
      (proofSize π : ℝ)  := by
  let k := ⌊(1/2-ε)*(n : ℝ)⌋₊
  have hrk : r^(d-1) ≤ k := by
    have he : ((r^(d-1) : ℕ) : ℝ) ≤ k := by
      simpa only [Nat.cast_pow] using hrn.trans (budget_le_cutoff hε₀ hε hn)
    exact_mod_cast he
  have hkn : k ≤ n := cutoff_le_n hε₀ hε
  have hp : r^(d-2) ≤ r^(d-1) := Nat.pow_le_pow_right hr (by omega)
  have hp' : ((r^(d-2) : ℕ) : ℝ) ≤ ε*n/2 := by
    have he : ((r^(d-2) : ℕ) : ℝ) ≤ ((r^(d-1) : ℕ) : ℝ) := by exact_mod_cast hp
    exact he.trans (by simpa only [Nat.cast_pow] using hrn)
  have hl := cumulative_ratio hε₀ hε hn (r^(d-2)) hp'
  have ht := cumulative_ratio hε₀ hε hn (r^(d-1)) (by simpa only [Nat.cast_pow] using hrn)
  simp only [Nat.cast_pow] at hl ht
  have hH : (0 : ℝ) < Hn n k := by exact_mod_cast BooleanDimension.Hn_pos n k
  have hal : (1/2 : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2))) ≤
      (Hn n (k-r^(d-2)) : ℝ)/(2*(Hn n k : ℝ)) := by
    calc
      _ ≤ (1/2 : ℝ)*((Hn n (k-r^(d-2)) : ℝ)/(Hn n k : ℝ)) := mul_le_mul_of_nonneg_left hl (by norm_num)
      _ = _ := by field_simp [ne_of_gt hH]
  have hat : (1/2 : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1))) ≤
      (Hn n (k-r^(d-1)) : ℝ)/(2*(Hn n k : ℝ)) := by
    calc
      _ ≤ (1/2 : ℝ)*((Hn n (k-r^(d-1)) : ℝ)/(Hn n k : ℝ)) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by field_simp [ne_of_gt hH]
  have hθ : (1/2 : ℝ)*min ((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2))))
        ((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1)))) ≤
      min ((r : ℝ)*((Hn n (k-r^(d-2)) : ℝ)/(2*(Hn n k : ℝ))))
        ((R : ℝ)*((Hn n (k-r^(d-1)) : ℝ)/(2*(Hn n k : ℝ)))) := by
    apply le_min
    · calc
        _ ≤ (1/2 : ℝ)*((r : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2)))) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        _ = (r : ℝ)*((1/2 : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-2)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hal (Nat.cast_nonneg _)
    · calc
        _ ≤ (1/2 : ℝ)*((R : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1)))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = (R : ℝ)*((1/2 : ℝ)*Real.exp (-(128*ε*(r : ℝ)^(d-1)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg _)
  have hbase := theorem_4_16_size_bound F d r R k hd hr hR hrk hkn U hU hred π hπ
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
    (div_nonneg (Nat.cast_nonneg _) hH.le)).trans hbase

end SemAC02.NumericalSizeBound
end

open Classical SemAC02 MvPolynomial

theorem solution {n : ℕ} (F : Set (Circ (Fin n))) (d r R : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 256)
    (hn : 16 / ε ^ 2 ≤ (n : ℝ)) (hrn : (r : ℝ) ^ (d - 1) ≤ ε * n / 2)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hU : U ≤ Ble (Fin n) ⌊(1 / 2 - ε) * (n : ℝ)⌋₊)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n ⌊(1 / 2 - ε) * (n : ℝ)⌋₊ : ℝ) *
        Real.exp (1 / 2 * min ((r : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 2))))
          ((R : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 1))))) ≤
      (proofSize π : ℝ)  := by
  exact SemAC02.NumericalSizeBound.corollary_size_bound F d r R hd hr hR ε hε₀ hε hn hrn U hU hred π hπ
