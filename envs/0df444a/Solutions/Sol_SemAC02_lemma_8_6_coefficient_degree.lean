-- Prove2me | solution 1 for SemAC02.lemma_8_6_coefficient_degree
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T13:10:13.362923+00:00
-- url     : https://prove2.me/submissions/2bb88584-7db9-454b-be3a-e6c19ee7bb66

import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Mathlib


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


open MvPolynomial SemAC02

/-- **Lemma 8.6 (Coefficient degree and locality)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.6, p.65): let
`f ∈ span{x_T : T ∈ L^n}` and `p ∈ B_v`. Then `deg c_S(fp) ≤ deg p` for `S ∈ L^n`. If `p`
involves only blocks indexed by `J ⊆ [n]`, then `c_S(fp)` depends only on `z_J`.

Here (p.65) `Ω = (Ω₀ ∪ Ω₁)^n` with fibres `Ω(z) = ∏_i Ω_{z_i}`, and for `u ∈ B_v` the coordinates
`c_S(u) ∈ B_n` are the unique functions of `z` with `u(X) = ∑_{S∈L^n} c_S(u)(z) x_S(X)` for every
`X ∈ Ω(z)` (46).

**Formalization Note** Stated for every antitone `g₀` with `g₀(X) ∧ g₀(X̄) = 0` (the assumptions
of §8.1–8.2 that the coordinates use). The coordinates of `fp` are given as any family `c`
satisfying the expansion identity on every fibre; by Lemma 8.5 (every fibre is nonempty and the
`x_S` form a basis on it) such a family is unique, so it is the paper's `c_S(fp)`. The degree of a
function on `{0,1}^n` is the least total degree of a polynomial computing it; `deg p` is bounded
by the total degree of the polynomial `p`. "`p` involves only blocks `J`": every variable
`(i, j)` of `p` has `i ∈ J`. -/
theorem solution {n m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hanti : Antitone g₀)
    (hdisj : ∀ X : Fin m → Bool, ¬ (g₀ X = true ∧ g₀ (fun j => !X j) = true))
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g₀ n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : {A : Finset (Fin n × Fin m) // IsLnSupport g₀ A} → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g₀ z X →
      eval (toF2 X) (f * p) = ∑ S, c S z * eval (toF2 X) (AC02Frege.xMon S.1)) :
    (∀ S, ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ p.totalDegree ∧
        ∀ z : Fin n → Bool, eval (toF2 z) r = c S z) ∧
    ∀ J : Finset (Fin n), (∀ v ∈ p.vars, v.1 ∈ J) →
      ∀ S (z z' : Fin n → Bool), (∀ i ∈ J, z i = z' i) → c S z = c S z' := by
  classical
  have hc' := SemAC02.FibreCoordinates.coordinates_unique g₀ hanti (f * p) c hc
  constructor
  · intro S
    have hdeg := SemAC02.CoefficientControl.coefficient_degree g₀ hanti f hf p S
    obtain ⟨r, hr, he⟩ := (SemAC02.CoordinateSpaces.mem_degreeSpace _).mp hdeg
    refine ⟨r, hr, ?_⟩
    intro z
    rw [hc' S z]
    exact he z
  · intro J hp S z z' hz
    have hl := SemAC02.CoefficientControl.coefficient_locality g₀ hanti f hf p J hp S
    rw [hc' S z, hc' S z']
    exact hl z z' hz

