-- Prove2me | solution 1 for SemAC02.Supplement.theorem_3_7_bphp_degree
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T14:47:21.796649+00:00
-- url     : https://prove2.me/submissions/4ccac512-6fcc-441e-b0c3-34ead5b3d69e

import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Mathlib
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_bphp
import Mathlib.Order.PiLex
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MBitPHPProof
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
-- Inlined Solutions.P2MMatchingPolynomialFunctions

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MMatchingPolynomialFunctions

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- A set of edges is a partial matching when no two distinct edges share an endpoint. -/
def IsMatching (A : Finset (L×R)) : Prop :=
  ∀ e ∈ A, ∀ f ∈ A, e.1 = f.1 ∨ e.2 = f.2 → e = f

abbrev Placements (L R : Type) := {A : Finset (L×R) // IsMatching A}

theorem matching_mono {A B : Finset (L×R)} (hAB : A ⊆ B) (hB : IsMatching B) : IsMatching A :=
  fun e he f hf hshare => hB e (hAB he) f (hAB hf) hshare

theorem matching_empty : IsMatching (∅ : Finset (L×R)) := by simp [IsMatching]

theorem matching_singleton (e : L×R) : IsMatching ({e} : Finset (L×R)) := by
  intro f hf g hg _
  exact (Finset.mem_singleton.mp hf).trans (Finset.mem_singleton.mp hg).symm

noncomputable def assignment (B : Placements L R) (e : L×R) : ZMod 2 := if e ∈ B.val then 1 else 0

noncomputable def evaluation : MvPolynomial (L×R) (ZMod 2) →ₗ[ZMod 2] (Placements L R → ZMod 2) where
  toFun p B := eval (assignment B) p
  map_add' p q := by
    funext B
    change eval (assignment B) (p+q) = eval (assignment B) p+eval (assignment B) q
    exact map_add (eval (assignment B)) p q
  map_smul' a p := by
    funext B
    change eval (assignment B) (a • p) = a • eval (assignment B) p
    exact smul_eval (assignment B) p a

noncomputable def monomial (A : Finset (L×R)) : Placements L R → ZMod 2 := evaluation (xMon A)

theorem monomial_value (A : Finset (L×R)) (B : Placements L R) :
    monomial A B = if A ⊆ B.val then 1 else 0 := P2MBooleanRestrictions.xMon_eval_point A B.val

theorem monomial_zero (A : Finset (L×R)) (hA : ¬ IsMatching A) : monomial A = 0 := by
  funext B
  have hnot : ¬ A ⊆ B.val := fun hh => hA (matching_mono hh B.property)
  simp only [monomial_value, if_neg hnot, Pi.zero_apply]

theorem monomial_mul (A B : Finset (L×R)) : monomial A*monomial B = monomial (A ∪ B) := by
  funext T
  simp only [Pi.mul_apply, monomial_value, Finset.union_subset_iff]
  by_cases hA : A ⊆ T.val <;> by_cases hB : B ⊆ T.val <;> simp [hA, hB]

theorem monomial_empty : monomial (∅ : Finset (L×R)) = 1 := by
  funext B
  simp only [monomial_value, Finset.empty_subset, if_true, Pi.one_apply]

theorem evaluation_injective (p q : MvPolynomial (L×R) (ZMod 2))
    (hp : p ∈ monomialSpan IsMatching) (hq : q ∈ monomialSpan IsMatching)
    (he : evaluation p = evaluation q) : p = q := by
  apply sub_eq_zero.mp
  apply P2MBooleanRestrictions.eval_injective_on_monomialSpan IsMatching (p-q)
    ((monomialSpan IsMatching).sub_mem hp hq)
  intro A hA
  have hh := congrFun he (⟨A, hA⟩ : Placements L R)
  rw [map_sub]
  exact sub_eq_zero.mpr hh

noncomputable def space (d : ℕ) : Submodule (ZMod 2) (Placements L R → ZMod 2) :=
  Submodule.span (ZMod 2) {p | ∃ A : Finset (L×R), IsMatching A ∧ A.card ≤ d ∧ p = monomial A}

theorem monomial_mem (A : Finset (L×R)) (hA : IsMatching A) (d : ℕ) (hd : A.card ≤ d) :
    monomial A ∈ space (L:=L) (R:=R) d := Submodule.subset_span ⟨A, hA, hd, rfl⟩

theorem one_mem (d : ℕ) : (1 : Placements L R → ZMod 2) ∈ space d := by
  rw [← monomial_empty]
  exact monomial_mem ∅ matching_empty d (by simp)

theorem space_mono {d e : ℕ} (hde : d ≤ e) : space (L:=L) (R:=R) d ≤ space e := by
  apply Submodule.span_le.mpr
  rintro p ⟨A, hA, hd, rfl⟩
  exact monomial_mem A hA e (hd.trans hde)

theorem mul_mem {d e : ℕ} {p q : Placements L R → ZMod 2} (hp : p ∈ space d) (hq : q ∈ space e) :
    p*q ∈ space (d+e) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨A, hA, hd, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨B, hB, he, rfl⟩ := hq
      rw [monomial_mul]
      by_cases hAB : IsMatching (A ∪ B)
      · exact monomial_mem _ hAB _ ((Finset.card_union_le _ _).trans (Nat.add_le_add hd he))
      · rw [monomial_zero _ hAB]
        exact (space _).zero_mem
    | zero => simpa only [mul_zero] using (space (L:=L) (R:=R) (d+e)).zero_mem
    | add q r hq hr ihq ihr => simpa only [mul_add] using (space _).add_mem ihq ihr
    | smul a q hq ih => simpa only [mul_smul_comm] using (space _).smul_mem a ih
  | zero => simpa only [zero_mul] using (space (L:=L) (R:=R) (d+e)).zero_mem
  | add p r hp hr ihp ihr => simpa only [add_mul] using (space _).add_mem ihp ihr
  | smul a p hp ih => simpa only [smul_mul_assoc] using (space _).smul_mem a ih

end ProofComplexity.P2MMatchingPolynomialFunctions
end

section
-- Inlined Solutions.P2MMatchingSubstitutionDegree

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MMatchingSubstitutionDegree

open MvPolynomial P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem pow_mem {p : Placements L R → ZMod 2} {d : ℕ} (hp : p ∈ space d) (k : ℕ) :
    p^k ∈ space (d*k) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.mul_zero] using (one_mem 0 (L:=L) (R:=R))
  | succ k ih =>
    simpa only [pow_succ, Nat.mul_succ, Nat.add_comm] using mul_mem ih hp

theorem prod_mem {I : Type*} (s : Finset I) (p : I → Placements L R → ZMod 2) (d : I → ℕ)
    (h : ∀ i ∈ s, p i ∈ space (d i)) : (∏ i ∈ s, p i) ∈ space (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using (one_mem 0 (L:=L) (R:=R))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem aeval_mem {V : Type} (x : V → Placements L R → ZMod 2)
    (hx : ∀ v, x v ∈ space 1) (p : MvPolynomial V (ZMod 2)) :
    aeval x p ∈ space p.totalDegree := by
  classical
  have he : aeval x p = ∑ s ∈ p.support, aeval x (MvPolynomial.monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  apply (space p.totalDegree).sum_mem
  intro s hs
  rw [aeval_monomial]
  have hprod : (s.prod fun v k => x v^k) ∈ space (s.sum fun _ k => k) := by
    unfold Finsupp.prod Finsupp.sum
    apply prod_mem
    intro v hv
    simpa only [Nat.one_mul] using pow_mem (hx v) (s v)
  have hscaled := (space (L:=L) (R:=R) (s.sum fun _ k => k)).smul_mem (coeff s p) hprod
  apply space_mono (le_totalDegree hs)
  simpa only [Algebra.smul_def] using hscaled

end ProofComplexity.P2MMatchingSubstitutionDegree
end

section
-- Inlined Solutions.P2MMatchingRowEquations

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MMatchingRowEquations

open P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

noncomputable def coordinate (e : L×R) : Placements L R → ZMod 2 := monomial {e}
noncomputable def equation (u : L) : Placements L R → ZMod 2 := 1-∑ v : R, coordinate (u, v)

theorem coordinate_value (e : L×R) (B : Placements L R) : coordinate e B = if e ∈ B.val then 1 else 0 := by
  simp only [coordinate, monomial_value, Finset.singleton_subset_iff]

theorem coordinate_mem (e : L×R) : coordinate e ∈ space (L:=L) (R:=R) 1 :=
  monomial_mem {e} (matching_singleton e) 1 (by simp)

theorem equation_mem (u : L) : equation (R:=R) u ∈ space (L:=L) (R:=R) 1 := by
  apply (space 1).sub_mem (one_mem 1)
  exact (space 1).sum_mem (fun v _ => coordinate_mem (u, v))

theorem row_sum_occupied (u : L) (B : Placements L R) (v : R) (hv : (u, v) ∈ B.val) :
    (∑ w : R, coordinate (u, w) B) = 1 := by
  classical
  rw [Finset.sum_eq_single v]
  · simp only [coordinate_value, if_pos hv]
  · intro w hw hwv
    have hnot : (u, w) ∉ B.val := by
      intro hh
      exact hwv (congrArg Prod.snd (B.property (u, w) hh (u, v) hv (Or.inl rfl)))
    simp only [coordinate_value, if_neg hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem equation_value (u : L) (B : Placements L R) :
    equation u B = if ∃ v, (u, v) ∈ B.val then 0 else 1 := by
  classical
  change (1 : ZMod 2)-(∑ v : R, coordinate (u, v)) B = _
  simp only [Finset.sum_apply]
  by_cases h : ∃ v, (u, v) ∈ B.val
  · obtain ⟨v, hv⟩ := h
    rw [if_pos ⟨v, hv⟩, row_sum_occupied u B v hv, sub_self]
  · rw [if_neg h]
    have hz : (∑ v : R, coordinate (u, v) B) = 0 := Finset.sum_eq_zero (fun v _ => by
      have hv : (u, v) ∉ B.val := fun hv => h ⟨v, hv⟩
      simp only [coordinate_value, if_neg hv])
    rw [hz, sub_zero]

theorem equation_idempotent (u : L) : equation (R:=R) u*equation u = equation u := by
  funext B
  simp only [Pi.mul_apply, equation_value]
  split_ifs <;> simp

theorem monomial_mul_equation_zero (A : Finset (L×R)) (u : L)
    (hrow : ∃ e ∈ A, e.1 = u) : monomial A*equation u = 0 := by
  funext B
  simp only [Pi.mul_apply, Pi.zero_apply, monomial_value, equation_value]
  by_cases hAB : A ⊆ B.val
  · obtain ⟨e, he, heu⟩ := hrow
    have hoccupied : ∃ v, (u, v) ∈ B.val := by
      refine ⟨e.2, ?_⟩
      have he' := hAB he
      simpa only [← heu, Prod.mk.eta] using he'
    rw [if_pos hAB, if_pos hoccupied, mul_zero]
  · rw [if_neg hAB, zero_mul]

end ProofComplexity.P2MMatchingRowEquations
end

section
-- Inlined Solutions.P2MPigeonDanceStep

set_option maxHeartbeats 2000000

namespace ProofComplexity.P2MPigeonDanceStep

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev State (L : Type) (n : ℕ) := L → Option (Fin (n+1))

/-- The distinguished value zero represents a row equation. Positive holes are unique. -/
def Valid (a : State L n) : Prop :=
  ∀ u v j, j ≠ 0 → a u = some j → a v = some j → u = v

noncomputable def available (a : State L n) (old : Fin (n+1)) : Finset (Fin (n+1)) :=
  open Classical in Finset.univ.filter (fun j => old < j ∧ ∀ u, a u ≠ some j)

noncomputable def advance (a : State L n) (i : L) (j : Fin (n+1)) : State L n :=
  Function.update a i (some j)

noncomputable def greedy (a : State L n) (i : L) : Option (State L n) :=
  match a i with
  | none => some a
  | some old => if h : (available a old).Nonempty then some (advance a i ((available a old).min' h)) else none

theorem mem_available (a : State L n) (old j : Fin (n+1)) :
    j ∈ available a old ↔ old < j ∧ ∀ u, a u ≠ some j := by
  classical
  simp [available]

theorem advance_valid (a : State L n) (ha : Valid a) (i : L) (old j : Fin (n+1))
    (hj : j ∈ available a old) : Valid (advance a i j) := by
  intro u v k hk hu hv
  obtain ⟨hgreater, hfree⟩ := (mem_available a old j).mp hj
  by_cases hui : u = i
  · subst u
    by_cases hvi : v = i
    · exact hvi.symm
    · have hjk : j = k := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
      have hv' : a v = some j := by
        simpa only [advance, Function.update_of_ne hvi, ← hjk] using hv
      exact (hfree v hv').elim
  · by_cases hvi : v = i
    · subst v
      have hjk : j = k := Option.some.inj (by simpa only [advance, Function.update_self] using hv)
      have hu' : a u = some j := by
        simpa only [advance, Function.update_of_ne hui, ← hjk] using hu
      exact (hfree u hu').elim
    · exact ha u v k hk (by simpa only [advance, Function.update_of_ne hui] using hu)
        (by simpa only [advance, Function.update_of_ne hvi] using hv)

theorem old_available (a b : State L n) (hb : Valid b) (i : L) (old new : Fin (n+1))
    (hai : a i = some old) (hbi : b i = some new) (hlt : old < new)
    (hothers : ∀ u, u ≠ i → a u = b u) : new ∈ available a old := by
  apply (mem_available a old new).mpr
  refine ⟨hlt, ?_⟩
  intro u hu
  by_cases hui : u = i
  · subst u
    have he := Option.some.inj (hai.symm.trans hu)
    exact (ne_of_lt hlt) he
  · have hnew : new ≠ 0 := by
      intro hz
      rw [hz] at hlt
      exact (not_lt_of_ge (Fin.zero_le old)) hlt
    have hu' : b u = some new := (hothers u hui).symm.trans hu
    exact hui (hb u i new hnew hu' hbi)

theorem advance_injective (a b : State L n) (ha : Valid a) (hb : Valid b) (i : L)
    (old new : Fin (n+1)) (hai : a i = some old) (hbi : b i = some new)
    (hA : (available a old).Nonempty) (hB : (available b new).Nonempty)
    (he : advance a i ((available a old).min' hA) = advance b i ((available b new).min' hB)) : a = b := by
  have hothers : ∀ u, u ≠ i → a u = b u := by
    intro u hu
    simpa only [advance, Function.update_of_ne hu] using congrFun he u
  have hmin : (available a old).min' hA = (available b new).min' hB :=
    Option.some.inj (by simpa only [advance, Function.update_self] using congrFun he i)
  have hold : old = new := by
    rcases lt_trichotomy old new with hlt | heq | hgt
    · have hav := old_available a b hb i old new hai hbi hlt hothers
      have hle := Finset.min'_le (available a old) new hav
      have hgreater := ((mem_available b new _).mp (Finset.min'_mem _ hB)).1
      rw [hmin] at hle
      exact (not_lt_of_ge hle hgreater).elim
    · exact heq
    · have hav := old_available b a ha i new old hbi hai hgt (fun u hu => (hothers u hu).symm)
      have hle := Finset.min'_le (available b new) old hav
      have hgreater := ((mem_available a old _).mp (Finset.min'_mem _ hA)).1
      rw [← hmin] at hle
      exact (not_lt_of_ge hle hgreater).elim
  funext u
  by_cases hui : u = i
  · subst u
    rw [hai, hbi, hold]
  · exact hothers u hui

theorem greedy_valid (a : State L n) (ha : Valid a) (i : L) (b : State L n)
    (he : greedy a i = some b) : Valid b := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rwa [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact advance_valid a ha i old _ (Finset.min'_mem _ hA)
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_injective (a b : State L n) (ha : Valid a) (hb : Valid b) (i : L) (c : State L n)
    (heA : greedy a i = some c) (heB : greedy b i = some c) : a = b := by
  classical
  cases hai : a i with
  | none =>
    have hac : a = c := Option.some.inj (by simpa only [greedy, hai] using heA)
    cases hbi : b i with
    | none =>
      have hbc : b = c := Option.some.inj (by simpa only [greedy, hbi] using heB)
      exact hac.trans hbc.symm
    | some old =>
      by_cases hB : (available b old).Nonempty
      · have hbc : advance b i ((available b old).min' hB) = c :=
          Option.some.inj (by simpa only [greedy, hbi, dif_pos hB] using heB)
        have hi := congrFun hbc i
        rw [← hac, hai] at hi
        simp only [advance, Function.update_self] at hi
        cases hi
      · simp only [greedy, hbi, dif_neg hB] at heB
        cases heB
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hac : advance a i ((available a old).min' hA) = c :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using heA)
      cases hbi : b i with
      | none =>
        have hbc : b = c := Option.some.inj (by simpa only [greedy, hbi] using heB)
        have hi := congrFun hac i
        rw [← hbc, hbi] at hi
        simp only [advance, Function.update_self] at hi
        cases hi
      | some new =>
        by_cases hB : (available b new).Nonempty
        · have hbc : advance b i ((available b new).min' hB) = c :=
            Option.some.inj (by simpa only [greedy, hbi, dif_pos hB] using heB)
          exact advance_injective a b ha hb i old new hai hbi hA hB (hac.trans hbc.symm)
        · simp only [greedy, hbi, dif_neg hB] at heB
          cases heB
    · simp only [greedy, hai, dif_neg hA] at heA
      cases heA

noncomputable def run : List L → State L n → Option (State L n)
  | [], a => some a
  | i::is, a => (greedy a i).bind (run is)

theorem run_valid (is : List L) (a b : State L n) (ha : Valid a) (he : run is a = some b) : Valid b := by
  induction is generalizing a b with
  | nil =>
    have hab := Option.some.inj he
    rwa [← hab]
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      apply ih c b (greedy_valid a ha i c hstep)
      simpa only [run, hstep, Option.bind_some] using he

theorem run_injective (is : List L) (a b c : State L n) (ha : Valid a) (hb : Valid b)
    (heA : run is a = some c) (heB : run is b = some c) : a = b := by
  induction is generalizing a b c with
  | nil => exact (Option.some.inj heA).trans (Option.some.inj heB).symm
  | cons i is ih =>
    cases hA : greedy a i with
    | none => simp only [run, hA, Option.bind_none] at heA; cases heA
    | some a' =>
      cases hB : greedy b i with
      | none => simp only [run, hB, Option.bind_none] at heB; cases heB
      | some b' =>
        have heA' : run is a' = some c := by simpa only [run, hA, Option.bind_some] using heA
        have heB' : run is b' = some c := by simpa only [run, hB, Option.bind_some] using heB
        have hab := ih a' b' c (greedy_valid a ha i a' hA) (greedy_valid b hb i b' hB) heA' heB'
        exact greedy_injective a b ha hb i a' hA (by rwa [hab])

end ProofComplexity.P2MPigeonDanceStep
end

section
-- Inlined Solutions.P2MPigeonDanceDomain

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceDomain

open P2MPigeonDanceStep

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def domain (a : State L n) : Finset L :=
  open Classical in Finset.univ.filter (fun u => ∃ j, a u = some j)

theorem mem_domain (a : State L n) (u : L) : u ∈ domain a ↔ ∃ j, a u = some j := by
  classical
  simp [domain]

theorem advance_domain (a : State L n) (i : L) (old j : Fin (n+1)) (hai : a i = some old) :
    domain (advance a i j) = domain a := by
  classical
  ext u
  rw [mem_domain, mem_domain]
  by_cases hui : u = i
  · subst u
    simp only [advance, Function.update_self, hai, Option.some.injEq, exists_eq']
  · simp only [advance, Function.update_of_ne hui]

theorem greedy_domain (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b) :
    domain b = domain a := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact advance_domain a i old _ hai
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_other (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b)
    (u : L) (hui : u ≠ i) : b u = a u := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab]
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      rw [← hab]
      exact Function.update_of_ne hui _ _
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem greedy_no_zero (a : State L n) (i : L) (b : State L n) (he : greedy a i = some b) : b i ≠ some 0 := by
  classical
  cases hai : a i with
  | none =>
    have hab : a = b := Option.some.inj (by simpa only [greedy, hai] using he)
    rw [← hab, hai]
    intro h
    cases h
  | some old =>
    by_cases hA : (available a old).Nonempty
    · have hab : advance a i ((available a old).min' hA) = b :=
        Option.some.inj (by simpa only [greedy, hai, dif_pos hA] using he)
      have hgreater := ((mem_available a old _).mp (Finset.min'_mem _ hA)).1
      intro hz
      rw [← hab] at hz
      have hj0 : (available a old).min' hA = 0 :=
        Option.some.inj (by simpa only [advance, Function.update_self] using hz)
      rw [hj0] at hgreater
      exact (not_lt_of_ge (Fin.zero_le old)) hgreater
    · simp only [greedy, hai, dif_neg hA] at he
      cases he

theorem run_domain (is : List L) (a b : State L n) (he : run is a = some b) : domain b = domain a := by
  induction is generalizing a b with
  | nil => rw [← Option.some.inj he]
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      exact (ih c b hr).trans (greedy_domain a i c hstep)

theorem run_other (is : List L) (a b : State L n) (he : run is a = some b)
    (u : L) (hu : u ∉ is) : b u = a u := by
  induction is generalizing a b with
  | nil => rw [← Option.some.inj he]
  | cons i is ih =>
    have hui : u ≠ i := fun h => hu (List.mem_cons.mpr (Or.inl h))
    have hu' : u ∉ is := fun h => hu (List.mem_cons.mpr (Or.inr h))
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      exact (ih c b hr hu').trans (greedy_other a i c hstep u hui)

theorem run_no_zero (is : List L) (a b : State L n) (he : run is a = some b)
    (u : L) (hu : u ∈ is) : b u ≠ some 0 := by
  induction is generalizing a b with
  | nil => simp only [List.not_mem_nil] at hu
  | cons i is ih =>
    cases hstep : greedy a i with
    | none => simp only [run, hstep, Option.bind_none] at he; cases he
    | some c =>
      have hr : run is c = some b := by simpa only [run, hstep, Option.bind_some] using he
      rcases List.mem_cons.mp hu with rfl | hu
      · by_cases hi : u ∈ is
        · exact ih c b hr hi
        · rw [run_other is c b hr u hi]
          exact greedy_no_zero a u c hstep
      · exact ih c b hr hu

end ProofComplexity.P2MPigeonDanceDomain
end

section
-- Inlined Solutions.P2MPigeonDancePolynomials

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDancePolynomials

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev Positive (n : ℕ) := {j : Fin (n+1) // j ≠ 0}

noncomputable def edges (a : State L n) : Finset (L×Positive n) :=
  open Classical in Finset.univ.filter (fun e => a e.1 = some e.2.val)

noncomputable def zeros (a : State L n) : Finset L :=
  open Classical in Finset.univ.filter (fun u => a u = some 0)

theorem mem_edges (a : State L n) (e : L×Positive n) : e ∈ edges a ↔ a e.1 = some e.2.val := by
  classical
  simp [edges]

theorem mem_zeros (a : State L n) (u : L) : u ∈ zeros a ↔ a u = some 0 := by
  classical
  simp [zeros]

theorem matching_edges (a : State L n) (ha : Valid a) : IsMatching (edges a) := by
  intro e he f hf hshare
  have he' := (mem_edges a e).mp he
  have hf' := (mem_edges a f).mp hf
  rcases hshare with hrow | hhole
  · have hv : e.2.val = f.2.val := Option.some.inj (he'.symm.trans (hrow ▸ hf'))
    exact Prod.ext hrow (Subtype.ext hv)
  · have hu : e.1 = f.1 := ha e.1 f.1 e.2.val e.2.property he' (by simpa only [hhole] using hf')
    exact Prod.ext hu hhole

theorem rows_edges (a : State L n) (u : L) :
    u ∈ (edges a).image Prod.fst ↔ ∃ j, a u = some j ∧ j ≠ 0 := by
  constructor
  · intro h
    obtain ⟨e, he, heu⟩ := Finset.mem_image.mp h
    exact ⟨e.2.val, by simpa only [heu] using (mem_edges a e).mp he, e.2.property⟩
  · rintro ⟨j, haj, hj⟩
    exact Finset.mem_image.mpr ⟨(u, ⟨j, hj⟩), (mem_edges a _).mpr haj, rfl⟩

theorem domain_card (a : State L n) : (edges a).card+(zeros a).card = (domain a).card := by
  classical
  have hrowinj : Set.InjOn Prod.fst (edges a : Set (L×Positive n)) := by
    intro e he f hf hrow
    have hv : e.2.val = f.2.val := Option.some.inj
      (((mem_edges a e).mp he).symm.trans (hrow ▸ (mem_edges a f).mp hf))
    exact Prod.ext hrow (Subtype.ext hv)
  have hdis : Disjoint ((edges a).image Prod.fst) (zeros a) := by
    apply Finset.disjoint_left.mpr
    intro u hu hz
    obtain ⟨j, hj, hj0⟩ := (rows_edges a u).mp hu
    exact hj0 (Option.some.inj (hj.symm.trans ((mem_zeros a u).mp hz)))
  have hdom : domain a = (edges a).image Prod.fst ∪ zeros a := by
    ext u
    rw [mem_domain, Finset.mem_union, rows_edges, mem_zeros]
    constructor
    · rintro ⟨j, hj⟩
      by_cases hj0 : j = 0
      · exact Or.inr (by rwa [hj0] at hj)
      · exact Or.inl ⟨j, hj, hj0⟩
    · rintro (⟨j, hj, _⟩ | hj)
      · exact ⟨j, hj⟩
      · exact ⟨0, hj⟩
  rw [hdom, Finset.card_union_of_disjoint hdis, Finset.card_image_iff.mpr hrowinj]

noncomputable def polynomial (a : State L n) : Placements L (Positive n) → ZMod 2 :=
  monomial (edges a)*∏ u ∈ zeros a, equation u

theorem product_equations_mem (A : Finset L) :
    (∏ u ∈ A, equation (R:=Positive n) u) ∈ space (L:=L) (R:=Positive n) A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.card_empty] using (one_mem 0 (L:=L) (R:=Positive n))
  | @insert u A hu ih =>
    rw [Finset.prod_insert hu, Finset.card_insert_of_notMem hu]
    simpa only [Nat.add_comm] using mul_mem (equation_mem (R:=Positive n) u) ih

theorem polynomial_mem (a : State L n) (ha : Valid a) : polynomial a ∈ space (L:=L) (R:=Positive n) (domain a).card := by
  have hh := mul_mem (monomial_mem (edges a) (matching_edges a ha) (edges a).card le_rfl)
    (product_equations_mem (n:=n) (zeros a))
  rw [domain_card] at hh
  exact hh

theorem zeros_eq_empty (a : State L n) (ha : ∀ u, a u ≠ some 0) : zeros a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact ha u ((mem_zeros a u).mp hu)

theorem edges_injective_no_zero (a b : State L n) (ha : ∀ u, a u ≠ some 0) (hb : ∀ u, b u ≠ some 0)
    (he : edges a = edges b) : a = b := by
  funext u
  cases hai : a u with
  | none =>
    cases hbi : b u with
    | none => rfl
    | some j =>
      have hj : j ≠ 0 := fun hh => hb u (by rwa [hh] at hbi)
      have hedge : (u, (⟨j, hj⟩ : Positive n)) ∈ edges b := (mem_edges b _).mpr hbi
      rw [← he] at hedge
      have hh := (mem_edges a _).mp hedge
      rw [hai] at hh
      cases hh
  | some j =>
    have hj : j ≠ 0 := fun hh => ha u (by rwa [hh] at hai)
    have hedge : (u, (⟨j, hj⟩ : Positive n)) ∈ edges a := (mem_edges a _).mpr hai
    rw [he] at hedge
    exact ((mem_edges b _).mp hedge).symm

end ProofComplexity.P2MPigeonDancePolynomials
end

section
-- Inlined Solutions.P2MBitPHPMatchingDecoding

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MBitPHPMatchingDecoding

open MvPolynomial P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials
open SemAC02.Supplement

variable {m n ℓ : ℕ}

noncomputable def bit (addr : Positive n ≃ (Fin ℓ → Bool)) (e : Fin m × Fin ℓ) :
    Placements (Fin m) (Positive n) → ZMod 2 :=
  ∑ j : Positive n, if addr j e.2 then coordinate (e.1, j) else 0

theorem bit_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (e : Fin m × Fin ℓ) :
    bit addr e ∈ space 1 := by
  apply (space 1).sum_mem
  intro j hj
  split_ifs
  · exact coordinate_mem _
  · exact (space 1).zero_mem

noncomputable def decoded (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) : Fin m × Fin ℓ → Bool :=
  fun e => decide (bit addr e B = 1)

theorem decoded_point (addr : Positive n ≃ (Fin ℓ → Bool)) (B : Placements (Fin m) (Positive n)) :
    (boolPt (decoded addr B) : Fin m × Fin ℓ → ZMod 2) = fun e => bit addr e B := by
  funext e
  rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (bit addr e B) with h | h <;>
    simp [boolPt, decoded, h]

theorem polynomial_value (addr : Positive n ≃ (Fin ℓ → Bool))
    (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) :
    (fun B => polyFn p (decoded addr B)) = aeval (bit addr) p := by
  funext B
  have he := MvPolynomial.comp_aeval_apply (bit addr) (Pi.evalAlgHom (ZMod 2) (fun _ => ZMod 2) B) p
  change aeval (bit addr) p B = aeval (fun e => bit addr e B) p at he
  rw [he]
  change eval (boolPt (decoded addr B)) p = eval (fun e => bit addr e B) p
  rw [decoded_point]

theorem polynomial_mem (addr : Positive n ≃ (Fin ℓ → Bool))
    (p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2)) :
    (fun B => polyFn p (decoded addr B)) ∈ space p.totalDegree := by
  rw [polynomial_value]
  exact P2MMatchingSubstitutionDegree.aeval_mem (bit addr) (bit_mem addr) p

theorem circuit_mem (addr : Positive n ≃ (Fin ℓ → Bool))
    (c : ACirc (ZMod 2) (Fin m × Fin ℓ)) :
    (fun B => cval c (decoded addr B)) ∈ space (fnDeg (cval c)) := by
  have hnonempty : {d : ℕ | ∃ p : MvPolynomial (Fin m × Fin ℓ) (ZMod 2),
      p.totalDegree ≤ d ∧ polyFn p = cval c}.Nonempty :=
    ⟨c.toPoly.totalDegree, c.toPoly, le_rfl, rfl⟩
  obtain ⟨p, hp, he⟩ := Nat.sInf_mem hnonempty
  have hmem := space_mono hp (polynomial_mem addr p)
  change (fun B => polyFn p (decoded addr B)) ∈ space (fnDeg (cval c)) at hmem
  simpa only [he] using hmem

theorem bit_occupied (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (j : Positive n) (hj : (u,j) ∈ B.val)
    (t : Fin ℓ) : bit addr (u,t) B = if addr j t then 1 else 0 := by
  classical
  simp only [bit, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp [coordinate_value, hj]
  · intro k hk hkj
    have hnot : (u,k) ∉ B.val := by
      intro hh
      exact hkj (congrArg Prod.snd (B.property (u,k) hh (u,j) hj (Or.inl rfl)))
    split_ifs <;> simp [coordinate_value, hnot]
  · simp

theorem decoded_occupied (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (j : Positive n) (hj : (u,j) ∈ B.val)
    (t : Fin ℓ) : decoded addr B (u,t) = addr j t := by
  simp only [decoded, bit_occupied addr B u j hj t]
  cases addr j t <;> simp

theorem decoded_absent (addr : Positive n ≃ (Fin ℓ → Bool))
    (B : Placements (Fin m) (Positive n)) (u : Fin m) (hu : ¬ ∃ j, (u,j) ∈ B.val)
    (t : Fin ℓ) : decoded addr B (u,t) = false := by
  have hbit : bit addr (u,t) B = 0 := by
    simp only [bit, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : (u,j) ∉ B.val := fun h => hu ⟨j,h⟩
    split_ifs <;> simp [coordinate_value, hnot]
  simp [decoded, hbit]

end ProofComplexity.P2MBitPHPMatchingDecoding
end

section
-- Inlined Solutions.P2MPigeonDanceRelation

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceRelation

open P2MPigeonDanceStep P2MPigeonDanceDomain

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

def Step (a : State L n) (i : L) (b : State L n) : Prop :=
  (a i = none ∧ b = a) ∨
    ∃ old new, a i = some old ∧ new ∈ available a old ∧ b = advance a i new

inductive Dance : List L → State L n → State L n → Prop
  | nil (a) : Dance [] a a
  | cons {i is a b c} : Step a i b → Dance is b c → Dance (i::is) a c

theorem step_valid {a b : State L n} {i : L} (ha : Valid a) (h : Step a i b) : Valid b := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, _, hnew, rfl⟩
  · exact ha
  · exact advance_valid a ha i old new hnew

theorem step_other {a b : State L n} {i u : L} (h : Step a i b) (hui : u ≠ i) : b u = a u := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, _, _, rfl⟩
  · rfl
  · exact Function.update_of_ne hui _ _

theorem step_domain {a b : State L n} {i : L} (h : Step a i b) : domain b = domain a := by
  rcases h with ⟨_, rfl⟩ | ⟨old, new, hai, _, rfl⟩
  · rfl
  · exact advance_domain a i old new hai

theorem dance_valid {is : List L} {a b : State L n} (ha : Valid a) (h : Dance is a b) : Valid b := by
  induction h with
  | nil => exact ha
  | cons hstep hrest ih => exact ih (step_valid ha hstep)

theorem dance_other {is : List L} {a b : State L n} (h : Dance is a b) (u : L) (hu : u ∉ is) : b u = a u := by
  induction h with
  | nil => rfl
  | @cons i is a b c hstep hrest ih =>
    have hui : u ≠ i := fun hh => hu (List.mem_cons.mpr (Or.inl hh))
    have hu' : u ∉ is := fun hh => hu (List.mem_cons.mpr (Or.inr hh))
    exact (ih hu').trans (step_other hstep hui)

noncomputable def relabel (σ : Equiv.Perm (Fin (n+1))) (a : State L n) : State L n :=
  fun u => (a u).map σ

theorem relabel_inverse (σ : Equiv.Perm (Fin (n+1))) (a : State L n) : relabel σ.symm (relabel σ a) = a := by
  funext u
  cases h : a u <;> simp [relabel, h]

theorem relabel_some (σ : Equiv.Perm (Fin (n+1))) (a : State L n) (u : L) (j : Fin (n+1)) :
    relabel σ a u = some (σ j) ↔ a u = some j := by
  cases h : a u <;> simp [relabel, h]

theorem relabel_advance (σ : Equiv.Perm (Fin (n+1))) (a : State L n) (i : L) (j : Fin (n+1)) :
    relabel σ (advance a i j) = advance (relabel σ a) i (σ j) := by
  funext u
  by_cases hui : u = i <;> simp [relabel, advance, Function.update_apply, hui]

theorem relabel_valid (σ : Equiv.Perm (Fin (n+1))) (hσ : σ 0 = 0) (a : State L n) (ha : Valid a) :
    Valid (relabel σ a) := by
  intro u v j hj hu hv
  have hj' : σ.symm j ≠ 0 := by
    intro hh
    apply hj
    have he := congrArg σ hh
    simpa only [Equiv.apply_symm_apply, hσ] using he
  apply ha u v (σ.symm j) hj'
  · apply (relabel_some σ a u (σ.symm j)).mp
    simpa only [Equiv.apply_symm_apply] using hu
  · apply (relabel_some σ a v (σ.symm j)).mp
    simpa only [Equiv.apply_symm_apply] using hv

theorem step_relabel (σ : Equiv.Perm (Fin (n+1))) (a b : State L n) (i : L) (h : Step a i b)
    (horder : ∀ old new, a i = some old → new ∈ available a old → σ old < σ new) :
    Step (relabel σ a) i (relabel σ b) := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hnew, rfl⟩
  · left
    exact ⟨by simp [relabel, hai], rfl⟩
  · right
    refine ⟨σ old, σ new, by simp [relabel, hai], ?_, relabel_advance σ a i new⟩
    apply (mem_available _ _ _).mpr
    refine ⟨horder old new hai hnew, ?_⟩
    intro u hu
    exact ((mem_available a old new).mp hnew).2 u ((relabel_some σ a u new).mp hu)

end ProofComplexity.P2MPigeonDanceRelation
end

section
-- Inlined Solutions.P2MPigeonDanceGreedyCompleteness

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MPigeonDanceGreedyCompleteness

open P2MPigeonDanceStep P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

/-- A smaller first move can replace a larger move: swap the two holes in all
future states. No unprocessed pigeon initially occupies either hole. -/
theorem swap_future (is : List L) (hnd : is.Nodup) (a b : State L n)
    (anchor : L) (hanchor : anchor ∉ is) (j k : Fin (n+1)) (hjk : j ≤ k)
    (hak : a anchor = some k)
    (hfree : ∀ u ∈ is, a u ≠ some j ∧ a u ≠ some k)
    (hDance : Dance is a b) : Dance is (relabel (Equiv.swap j k) a) (relabel (Equiv.swap j k) b) := by
  induction is generalizing a b with
  | nil => cases hDance; exact Dance.nil _
  | cons i is ih =>
    obtain ⟨hinot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      have hanchor_i : anchor ≠ i := fun hh => hanchor (List.mem_cons.mpr (Or.inl hh))
      have hanchor' : anchor ∉ is := fun hh => hanchor (List.mem_cons.mpr (Or.inr hh))
      have hiFree := hfree i List.mem_cons_self
      have horder : ∀ old new, a i = some old → new ∈ available a old →
          (Equiv.swap j k) old < (Equiv.swap j k) new := by
        intro old new hai hnew
        have holdj : old ≠ j := fun hh => hiFree.1 (by rwa [← hh])
        have holdk : old ≠ k := fun hh => hiFree.2 (by rwa [← hh])
        have hnewk : new ≠ k := by
          intro hh
          have hfreeNew := ((mem_available a old new).mp hnew).2
          exact hfreeNew anchor (by rwa [hh])
        have hOld : (Equiv.swap j k) old = old := by simp [Equiv.swap_apply_def, holdj, holdk]
        rw [hOld]
        by_cases hnewj : new = j
        · rw [hnewj, Equiv.swap_apply_left]
          have holdj' : old < j := by simpa only [hnewj] using ((mem_available a old new).mp hnew).1
          exact holdj'.trans_le hjk
        · simpa only [Equiv.swap_apply_def, if_neg hnewj, if_neg hnewk] using
            ((mem_available a old new).mp hnew).1
      apply Dance.cons (step_relabel (Equiv.swap j k) a c i hstep horder)
      apply ih hnd' c b hanchor' ?_ ?_ hrest
      · exact (step_other hstep hanchor_i).trans hak
      · intro u hu
        have hui : u ≠ i := by intro hh; exact hinot (hh ▸ hu)
        rw [step_other hstep hui]
        exact hfree u (List.mem_cons.mpr (Or.inr hu))

theorem relabel_free (a : State L n) (j k : Fin (n+1))
    (hj : ∀ u, a u ≠ some j) (hk : ∀ u, a u ≠ some k) : relabel (Equiv.swap j k) a = a := by
  funext u
  cases hai : a u with
  | none => simp [relabel, hai]
  | some old =>
    have holdj : old ≠ j := fun hh => hj u (by rwa [← hh])
    have holdk : old ≠ k := fun hh => hk u (by rwa [← hh])
    simp [relabel, hai, Equiv.swap_apply_def, holdj, holdk]

/-- If any legal sequence moves every pigeon in the list, the greedy sequence
also succeeds (the minimal pigeon-dance lemma). -/
theorem complete (is : List L) (hnd : is.Nodup) (a b : State L n) (hDance : Dance is a b) :
    ∃ c, run is a = some c := by
  classical
  induction is generalizing a b with
  | nil => exact ⟨a, rfl⟩
  | cons i is ih =>
    obtain ⟨hinot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      rcases hstep with ⟨hai, rfl⟩ | ⟨old, k, hai, hk, rfl⟩
      · obtain ⟨b', hb'⟩ := ih hnd' c b hrest
        exact ⟨b', by simpa only [run, greedy, hai, Option.bind_some] using hb'⟩
      · have hA : (available a old).Nonempty := ⟨k, hk⟩
        let j := (available a old).min' hA
        have hj : j ∈ available a old := Finset.min'_mem _ hA
        have hjk : j ≤ k := Finset.min'_le _ k hk
        have haj : ∀ u, a u ≠ some j := ((mem_available a old j).mp hj).2
        have hak : ∀ u, a u ≠ some k := ((mem_available a old k).mp hk).2
        have hrel : relabel (Equiv.swap j k) (advance a i k) = advance a i j := by
          rw [relabel_advance, relabel_free a j k haj hak, Equiv.swap_apply_right]
        have hfree : ∀ u ∈ is, advance a i k u ≠ some j ∧ advance a i k u ≠ some k := by
          intro u hu
          have hui : u ≠ i := by intro hh; exact hinot (hh ▸ hu)
          simp only [advance, Function.update_of_ne hui]
          exact ⟨haj u, hak u⟩
        have hnewDance := swap_future is hnd' (advance a i k) b i hinot j k hjk
          (by simp only [advance, Function.update_self]) hfree hrest
        rw [hrel] at hnewDance
        obtain ⟨b', hb'⟩ := ih hnd' (advance a i j) (relabel (Equiv.swap j k) b) hnewDance
        refine ⟨b', ?_⟩
        simpa only [run, greedy, hai, dif_pos hA, Option.bind_some, j] using hb'

end ProofComplexity.P2MPigeonDanceGreedyCompleteness
end

section
-- Inlined Solutions.P2MMatchingFunctionBasis

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MMatchingFunctionBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis P2MMatchingPolynomialFunctions

variable {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem independent : LinearIndependent (ZMod 2) (fun A : Placements L R => monomial A.val) := by
  let U := monomialSpan (IsMatching (L:=L) (R:=R))
  have hmem (A : Placements L R) : xMon A.val ∈ U := Submodule.subset_span ⟨A.val, A.property, rfl⟩
  let b (A : Placements L R) : U := ⟨xMon A.val, hmem A⟩
  have hb : LinearIndependent (ZMod 2) b := by
    apply LinearIndependent.of_comp U.subtype
    exact xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  let E := (evaluation (L:=L) (R:=R)).comp U.subtype
  have hE : Function.Injective E := by
    intro p q he
    apply Subtype.ext
    exact evaluation_injective p.val q.val p.property q.property he
  exact hb.map' E (LinearMap.ker_eq_bot.mpr hE)

abbrev DegreeIndex (L R : Type) (d : ℕ) := {A : Placements L R // A.val.card ≤ d}

theorem span_degree (d : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex L R d => monomial A.val.val)) =
      space (L:=L) (R:=R) d := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.val.val, A.val.property, A.property, rfl⟩
  · rintro ⟨A, hA, hd, rfl⟩
    exact ⟨⟨⟨A, hA⟩, hd⟩, rfl⟩

noncomputable def degreeBasis (d : ℕ) : Basis (DegreeIndex L R d) (ZMod 2) (space (L:=L) (R:=R) d) :=
  (Basis.span (independent.comp (fun A : DegreeIndex L R d => A.val) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree d))

instance finite_space (d : ℕ) : Module.Finite (ZMod 2) (space (L:=L) (R:=R) d) := by
  classical
  exact Module.Finite.of_basis (degreeBasis d)

theorem finrank_space (d : ℕ) : Module.finrank (ZMod 2) (space (L:=L) (R:=R) d) =
    Nat.card (DegreeIndex L R d) := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis d), Nat.card_eq_fintype_card]

end ProofComplexity.P2MMatchingFunctionBasis
end

section
-- Inlined Solutions.P2MPigeonDanceCounting

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDanceCounting

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

abbrev GoodState (is : List L) (d : ℕ) :=
  {a : State L n // Valid a ∧ (domain a).card ≤ d ∧ ∃ b, Dance is a b}

noncomputable def output (is : List L) (hnd : is.Nodup) (d : ℕ) (a : GoodState (n:=n) is d) : State L n :=
  Classical.choose (P2MPigeonDanceGreedyCompleteness.complete is hnd a.val
    (Classical.choose a.property.2.2) (Classical.choose_spec a.property.2.2))

theorem output_spec (is : List L) (hnd : is.Nodup) (d : ℕ) (a : GoodState (n:=n) is d) :
    run is a.val = some (output is hnd d a) :=
  Classical.choose_spec (P2MPigeonDanceGreedyCompleteness.complete is hnd a.val
    (Classical.choose a.property.2.2) (Classical.choose_spec a.property.2.2))

noncomputable def index (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ)
    (a : GoodState (n:=n) is d) : P2MMatchingFunctionBasis.DegreeIndex L (Positive n) d := by
  let b := output is hnd d a
  have hrun : run is a.val = some b := output_spec is hnd d a
  have hvalid : Valid b := run_valid is a.val b a.property.1 hrun
  refine ⟨⟨edges b, matching_edges b hvalid⟩, ?_⟩
  change (edges b).card ≤ d
  have hh := domain_card b
  have hdom := run_domain is a.val b hrun
  have hbound := a.property.2.1
  rw [hdom] at hh
  omega

theorem index_injective (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ) :
    Function.Injective (index (n:=n) is hnd hcovers d) := by
  intro a b he
  have hedges : edges (output is hnd d a) = edges (output is hnd d b) :=
    congrArg (fun A : P2MMatchingFunctionBasis.DegreeIndex L (Positive n) d => A.val.val) he
  have hout := edges_injective_no_zero (output is hnd d a) (output is hnd d b)
    (fun u => run_no_zero is a.val _ (output_spec is hnd d a) u (hcovers u))
    (fun u => run_no_zero is b.val _ (output_spec is hnd d b) u (hcovers u)) hedges
  apply Subtype.ext
  exact run_injective is a.val b.val (output is hnd d a) a.property.1 b.property.1
    (output_spec is hnd d a) (by rw [hout]; exact output_spec is hnd d b)

theorem count_le_dimension (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is) (d : ℕ) :
    Nat.card (GoodState (n:=n) is d) ≤ Module.finrank (ZMod 2) (space (L:=L) (R:=Positive n) d) := by
  rw [P2MMatchingFunctionBasis.finrank_space]
  exact Nat.card_le_card_of_injective (index is hnd hcovers d) (index_injective is hnd hcovers d)

end ProofComplexity.P2MPigeonDanceCounting
end

section
-- Inlined Solutions.P2MPigeonDanceOneRowExtension

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MPigeonDanceOneRowExtension

open P2MPigeonDanceStep P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem step_absent {a b : State L n} {i k : L} (h : Step a k b) (hai : a i = none) : b i = none := by
  by_cases hik : i = k
  · subst k
    rcases h with ⟨_, rfl⟩ | ⟨old, new, hsome, _, _⟩
    · exact hai
    · rw [hai] at hsome
      cases hsome
  · exact (step_other h hik).trans hai

theorem dance_absent {is : List L} {a b : State L n} {i : L} (h : Dance is a b) (hai : a i = none) : b i = none := by
  induction h with
  | nil => exact hai
  | cons hstep hrest ih => exact ih (step_absent hstep hai)

theorem step_no_zero {a b : State L n} {i : L} (h : Step a i b) : b i ≠ some 0 := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hnew, rfl⟩
  · rw [hai]
    intro hh
    cases hh
  · intro hh
    have hnew0 : new = 0 := Option.some.inj (by simpa only [advance, Function.update_self] using hh)
    have hgt := ((mem_available a old new).mp hnew).1
    rw [hnew0] at hgt
    exact (not_lt_of_ge (Fin.zero_le old)) hgt

theorem advance_commute (a : State L n) (i k : L) (j h : Fin (n+1)) (hik : i ≠ k) :
    advance (advance a i j) k h = advance (advance a k h) i j := by
  funext u
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    simp_all [advance, Function.update_apply]

theorem step_add_fixed {a b : State L n} {i k : L} (j : Fin (n+1)) (hik : i ≠ k)
    (h : Step a k b) (hnew : b k ≠ some j) : Step (advance a i j) k (advance b i j) := by
  rcases h with ⟨hai, rfl⟩ | ⟨old, new, hai, hfree, rfl⟩
  · left
    exact ⟨by simpa only [advance, Function.update_of_ne hik.symm] using hai, rfl⟩
  · have hnej : new ≠ j := by
      intro hh
      apply hnew
      simp only [advance, Function.update_self, hh]
    right
    refine ⟨old, new, by simpa only [advance, Function.update_of_ne hik.symm] using hai, ?_, ?_⟩
    · apply (mem_available _ old new).mpr
      refine ⟨((mem_available a old new).mp hfree).1, ?_⟩
      intro u hu
      by_cases hui : u = i
      · subst u
        have hh : j = new := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
        exact hnej hh.symm
      · exact ((mem_available a old new).mp hfree).2 u
          (by simpa only [advance, Function.update_of_ne hui] using hu)
    · exact (advance_commute a i k j new hik).symm

theorem free_next {is : List L} {a c b : State L n} {k : L} (hk : k ∉ is)
    (hstep : Step a k c) (hrest : Dance is c b) (h : Fin (n+1))
    (ha : ∀ u, a u ≠ some h) (hb : ∀ u, b u ≠ some h) : ∀ u, c u ≠ some h := by
  intro u
  by_cases huk : u = k
  · subst u
    rw [← dance_other hrest k hk]
    exact hb k
  · rw [step_other hstep huk]
    exact ha u

theorem anchor_move (a : State L n) (i : L) (h : Fin (n+1)) (hpos : h ≠ 0)
    (hfree : ∀ u, a u ≠ some h) : Step (advance a i 0) i (advance a i h) := by
  right
  refine ⟨0, h, by simp only [advance, Function.update_self], ?_, ?_⟩
  · apply (mem_available _ 0 h).mpr
    refine ⟨lt_of_le_of_ne (Fin.zero_le h) hpos.symm, ?_⟩
    intro u hu
    by_cases hui : u = i
    · subst u
      have hh : (0 : Fin (n+1)) = h := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
      exact hpos hh.symm
    · exact hfree u (by simpa only [advance, Function.update_of_ne hui] using hu)
  · funext u
    by_cases hui : u = i <;> simp [advance, Function.update_apply, hui]

/-- Insert an absent row into a legal dance. It starts at zero and takes a
positive hole unused by the original initial and final states. -/
theorem extend (is : List L) (hnd : is.Nodup) (a b : State L n) (i : L) (hai : a i = none)
    (h : Fin (n+1)) (hpos : h ≠ 0) (hfreeA : ∀ u, a u ≠ some h) (hfreeB : ∀ u, b u ≠ some h)
    (hDance : Dance is a b) :
    Dance is (advance a i (if i ∈ is then 0 else h)) (advance b i h) := by
  classical
  induction is generalizing a b with
  | nil =>
    cases hDance
    simp only [List.not_mem_nil, if_false]
    exact Dance.nil _
  | cons k is ih =>
    obtain ⟨hknot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hDance with
    | @cons _ _ _ c _ hstep hrest =>
      have hci := step_absent hstep hai
      have hfreeC := free_next hknot hstep hrest h hfreeA hfreeB
      by_cases hik : i = k
      · subst k
        have hca : c = a := by
          rcases hstep with ⟨_, hca⟩ | ⟨old, new, hsome, _, _⟩
          · exact hca
          · rw [hai] at hsome
            cases hsome
        subst c
        have hTail := ih hnd' a b hai hfreeA hfreeB hrest
        simp only [if_neg hknot] at hTail
        simp only [List.mem_cons_self, if_true]
        exact Dance.cons (anchor_move a i h hpos hfreeA) hTail
      · have hTail := ih hnd' c b hci hfreeC hfreeB hrest
        have hAllowed : c k ≠ some (if i ∈ is then 0 else h) := by
          split_ifs
          · exact step_no_zero hstep
          · exact hfreeC k
        have hHead := step_add_fixed (if i ∈ is then 0 else h) hik hstep hAllowed
        have hmem : (i ∈ k::is) ↔ i ∈ is := by simp only [List.mem_cons, hik, false_or]
        simp only [hmem]
        exact Dance.cons hHead hTail

end ProofComplexity.P2MPigeonDanceOneRowExtension
end

section
-- Inlined Solutions.P2MPigeonDanceUnusedHole

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDanceUnusedHole

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MPigeonDanceRelation

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def holes (a : State L n) : Finset (Positive n) :=
  open Classical in Finset.univ.filter (fun j => ∃ u, a u = some j.val)

theorem mem_holes (a : State L n) (j : Positive n) : j ∈ holes a ↔ ∃ u, a u = some j.val := by
  classical
  simp [holes]

theorem holes_card (a : State L n) : (holes a).card ≤ (domain a).card := by
  classical
  let u (j : holes a) : L := Classical.choose ((mem_holes a j.val).mp j.property)
  have hu (j : holes a) : a (u j) = some j.val.val := Classical.choose_spec ((mem_holes a j.val).mp j.property)
  let f : holes a → domain a := fun j => ⟨u j, (mem_domain a _).mpr ⟨j.val.val, hu j⟩⟩
  have hf : Function.Injective f := by
    intro j k he
    have heU : u j = u k := congrArg Subtype.val he
    have hh : some j.val.val = some k.val.val := (hu j).symm.trans (by rw [heU]; exact hu k)
    exact Subtype.ext (Subtype.ext (Option.some.inj hh))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem positive_card (n : ℕ) : Fintype.card (Positive n) = n := by
  let e : Positive n ≃ Fin n :=
    { toFun := fun j => j.val.pred j.property
      invFun := fun j => ⟨j.succ, Fin.succ_ne_zero j⟩
      left_inv := by intro j; exact Subtype.ext (Fin.succ_pred j.val j.property)
      right_inv := by intro j; exact Fin.pred_succ j }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem unused (a b : State L n) (hsmall : (domain a).card+(domain b).card < n) :
    ∃ h : Fin (n+1), h ≠ 0 ∧ (∀ u, a u ≠ some h) ∧ (∀ u, b u ≠ some h) := by
  classical
  have hcard : (holes a ∪ holes b).card < (Finset.univ : Finset (Positive n)).card := by
    rw [Finset.card_univ, positive_card]
    exact ((Finset.card_union_le _ _).trans (Nat.add_le_add (holes_card a) (holes_card b))).trans_lt hsmall
  obtain ⟨j, hj, hjnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨j.val, j.property, ?_, ?_⟩
  · intro u hu
    exact hjnot (Finset.mem_union_left _ ((mem_holes a j).mpr ⟨u, hu⟩))
  · intro u hu
    exact hjnot (Finset.mem_union_right _ ((mem_holes b j).mpr ⟨u, hu⟩))

theorem dance_domain {is : List L} {a b : State L n} (hDance : Dance is a b) : domain b = domain a := by
  induction hDance with
  | nil => rfl
  | cons hstep hrest ih => exact ih.trans (step_domain hstep)

/-- Adding a new row equation preserves the existence of a dance below half
the number of positive holes. Only one unused hole is needed. -/
theorem insert_zero (is : List L) (hnd : is.Nodup) (a b : State L n)
    (i : L) (hi : i ∈ is) (hai : a i = none)
    (hsmall : 2*((domain a).card+1) ≤ n) (hDance : Dance is a b) :
    ∃ c, Dance is (advance a i 0) c := by
  have hdomain := dance_domain hDance
  obtain ⟨h, hpos, hA, hB⟩ := unused a b (by rw [hdomain]; omega)
  have hExt := P2MPigeonDanceOneRowExtension.extend is hnd a b i hai h hpos hA hB hDance
  refine ⟨advance b i h, ?_⟩
  simpa only [if_pos hi] using hExt

end ProofComplexity.P2MPigeonDanceUnusedHole
end

section
-- Inlined Solutions.P2MPigeonDanceInsertZero

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceInsertZero

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem valid (a : State L n) (ha : Valid a) (i : L) : Valid (advance a i 0) := by
  intro u v j hj hu hv
  by_cases hui : u = i
  · subst u
    have hz : (0 : Fin (n+1)) = j := Option.some.inj (by simpa only [advance, Function.update_self] using hu)
    exact (hj hz.symm).elim
  · by_cases hvi : v = i
    · subst v
      have hz : (0 : Fin (n+1)) = j := Option.some.inj (by simpa only [advance, Function.update_self] using hv)
      exact (hj hz.symm).elim
    · exact ha u v j hj (by simpa only [advance, Function.update_of_ne hui] using hu)
        (by simpa only [advance, Function.update_of_ne hvi] using hv)

theorem edges (a : State L n) (i : L) (hai : a i = none) :
    P2MPigeonDancePolynomials.edges (advance a i 0) = P2MPigeonDancePolynomials.edges a := by
  ext e
  rw [mem_edges, mem_edges]
  by_cases hei : e.1 = i
  · simp only [hei, advance, Function.update_self, hai, Option.some.injEq]
    constructor
    · intro hh
      exact (e.2.property hh.symm).elim
    · intro hh
      cases hh
  · simp only [advance, Function.update_of_ne hei]

theorem zeros (a : State L n) (i : L) : P2MPigeonDancePolynomials.zeros (advance a i 0) = insert i (P2MPigeonDancePolynomials.zeros a) := by
  ext u
  rw [mem_zeros, Finset.mem_insert, mem_zeros]
  by_cases hui : u = i <;> simp [advance, Function.update_apply, hui]

theorem not_mem_zeros (a : State L n) (i : L) (hai : a i = none) : i ∉ P2MPigeonDancePolynomials.zeros a := by
  rw [mem_zeros, hai]
  intro h
  cases h

theorem polynomial (a : State L n) (i : L) (hai : a i = none) :
    P2MPigeonDancePolynomials.polynomial (advance a i 0) = P2MPigeonDancePolynomials.polynomial a*equation i := by
  classical
  unfold P2MPigeonDancePolynomials.polynomial
  rw [edges a i hai, zeros, Finset.prod_insert (not_mem_zeros a i hai)]
  ring

end ProofComplexity.P2MPigeonDanceInsertZero
end

section
-- Inlined Solutions.P2MPigeonDanceRowMultiplication

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceRowMultiplication

open P2MPigeonDanceStep P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem positive_zero (a : State L n) (i : L) (j : Fin (n+1)) (hj : j ≠ 0) (hai : a i = some j) :
    polynomial a*equation i = 0 := by
  have hrow : ∃ e ∈ edges a, e.1 = i := ⟨(i, ⟨j, hj⟩), (mem_edges a _).mpr hai, rfl⟩
  have hz := monomial_mul_equation_zero (edges a) i hrow
  calc
    _ = (monomial (edges a)*equation i)*(∏ u ∈ zeros a, equation u) := by unfold polynomial; ring
    _ = 0 := by rw [hz, zero_mul]

theorem zero_self (a : State L n) (i : L) (hai : a i = some 0) : polynomial a*equation i = polynomial a := by
  classical
  have hi : i ∈ zeros a := (mem_zeros a i).mpr hai
  let p := monomial (edges a)*∏ u ∈ (zeros a).erase i, equation u
  have he : polynomial a = p*equation i := by
    unfold polynomial p
    rw [← Finset.mul_prod_erase (zeros a) (fun u => equation (R:=Positive n) u) hi]
    ring
  rw [he, mul_assoc, equation_idempotent]

end ProofComplexity.P2MPigeonDanceRowMultiplication
end

section
-- Inlined Solutions.P2MPigeonDanceGoodSpan

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MPigeonDanceGoodSpan

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceDomain P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def span (is : List L) (d : ℕ) : Submodule (ZMod 2) (Placements L (Positive n) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun a : GoodState (n:=n) is d => polynomial a.val))

theorem basis_mem (is : List L) (d : ℕ) (a : GoodState (n:=n) is d) : polynomial a.val ∈ span is d :=
  Submodule.subset_span ⟨a, rfl⟩

theorem span_le_degree (is : List L) (d : ℕ) : span (n:=n) is d ≤ space (L:=L) (R:=Positive n) d := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, rfl⟩
  exact space_mono a.property.2.1 (polynomial_mem a.val a.property.1)

theorem span_mono (is : List L) {d e : ℕ} (hde : d ≤ e) : span (n:=n) is d ≤ span is e := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, rfl⟩
  exact basis_mem is e ⟨a.val, a.property.1, a.property.2.1.trans hde, a.property.2.2⟩

theorem mul_equation (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is)
    (d : ℕ) (hd : 1 ≤ d) (hbudget : 2*d ≤ n) (i : L)
    (p : Placements L (Positive n) → ZMod 2) (hp : p ∈ span is (d-1)) : p*equation i ∈ span is d := by
  classical
  have hle : span (n:=n) is (d-1) ≤ (span is d).comap (LinearMap.mulRight (ZMod 2) (equation i)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, rfl⟩
    change polynomial a.val*equation i ∈ span is d
    cases hai : a.val i with
    | none =>
      have hcard : (domain (advance a.val i 0)).card = (domain a.val).card+1 := by
        have hh := domain_card (advance a.val i 0)
        rw [P2MPigeonDanceInsertZero.edges a.val i hai, P2MPigeonDanceInsertZero.zeros,
          Finset.card_insert_of_notMem (P2MPigeonDanceInsertZero.not_mem_zeros a.val i hai)] at hh
        have hh' := domain_card a.val
        omega
      obtain ⟨b, hDance⟩ := a.property.2.2
      have hsmall : 2*((domain a.val).card+1) ≤ n := by
        have hh := a.property.2.1
        omega
      obtain ⟨c, hc⟩ := P2MPigeonDanceUnusedHole.insert_zero is hnd a.val b i (hcovers i) hai hsmall hDance
      let a' : GoodState (n:=n) is d := ⟨advance a.val i 0,
        P2MPigeonDanceInsertZero.valid a.val a.property.1 i, by rw [hcard]; have hh := a.property.2.1; omega, ⟨c, hc⟩⟩
      rw [← P2MPigeonDanceInsertZero.polynomial a.val i hai]
      exact basis_mem is d a'
    | some j =>
      by_cases hj : j = 0
      · have hai0 : a.val i = some 0 := by rwa [hj] at hai
        rw [P2MPigeonDanceRowMultiplication.zero_self a.val i hai0]
        exact span_mono is (Nat.sub_le d 1) (basis_mem is (d-1) a)
      · rw [P2MPigeonDanceRowMultiplication.positive_zero a.val i j hj hai]
        exact (span is d).zero_mem
  exact hle hp

end ProofComplexity.P2MPigeonDanceGoodSpan
end

section
-- Inlined Solutions.P2MPigeonDanceFiniteOrder

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceFiniteOrder

open P2MPigeonDanceStep

noncomputable def suffix (m k : ℕ) : List (Fin m) := (List.finRange m).drop k

theorem mem_suffix (m k : ℕ) (u : Fin m) : u ∈ suffix m k ↔ k ≤ u.val := by
  rw [suffix, List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hv := congrArg Fin.val he
    simp only [List.getElem_finRange, Fin.coe_cast, Fin.val_mk] at hv
    omega
  · intro hu
    refine ⟨u.val-k, by simp only [List.length_finRange]; omega, ?_⟩
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.coe_cast, Fin.val_mk]
    omega

theorem suffix_cons (m k : ℕ) (hk : k < m) : suffix m k = ⟨k, hk⟩::suffix m (k+1) := by
  have hlen : k < (List.finRange m).length := by simpa only [List.length_finRange] using hk
  simpa only [List.getElem_finRange, suffix, Fin.cast_mk] using (List.getElem_cons_drop hlen).symm

theorem suffix_empty (m k : ℕ) (hk : m ≤ k) : suffix m k = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp only [suffix, List.length_drop, List.length_finRange, Nat.sub_eq_zero_of_le hk]

theorem suffix_nodup (m k : ℕ) : (suffix m k).Nodup := (List.nodup_finRange m).drop

theorem suffix_covers (m : ℕ) (u : Fin m) : u ∈ suffix m 0 := (mem_suffix m 0 u).mpr (Nat.zero_le _)

def code {m n : ℕ} (a : State (Fin m) n) : Fin m → Fin (n+2) := fun u => (a u).elim 0 Fin.succ

local instance indexWellFounded (m : ℕ) : WellFoundedGT (Fin m) := ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

def Before {m n : ℕ} (a b : State (Fin m) n) : Prop := toColex (code a) < toColex (code b)

theorem before_wellFounded (m n : ℕ) : WellFounded (Before (m:=m) (n:=n)) := by
  classical
  letI : Fintype (Colex (Fin m → Fin (n+2))) := Fintype.ofEquiv _ toColex
  have h : WellFounded ((· < ·) : Colex (Fin m → Fin (n+2)) → Colex (Fin m → Fin (n+2)) → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  exact InvImage.wf (fun a => toColex (code a)) h

theorem before_of_lower {m n : ℕ} (a b : State (Fin m) n) (i : Fin m) (j k : Fin (n+1))
    (hai : a i = some j) (hbi : b i = some k) (hjk : j < k)
    (hfuture : ∀ u, i < u → a u = b u) : Before a b := by
  change Pi.Lex (· > ·) (· < ·) (code a) (code b)
  refine ⟨i, ?_, ?_⟩
  · intro u hu
    simp only [code, hfuture u hu]
  · simpa only [code, hai, hbi, Option.elim_some] using (Fin.succ_lt_succ_iff.mpr hjk)

end ProofComplexity.P2MPigeonDanceFiniteOrder
end

section
-- Inlined Solutions.P2MPigeonDanceRowErasure

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDanceRowErasure

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions P2MMatchingRowEquations

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

def Pure (a : State L n) : Prop := ∀ u, a u ≠ some 0

noncomputable def erase (a : State L n) (i : L) : State L n := Function.update a i none

theorem erase_pure (a : State L n) (ha : Pure a) (i : L) : Pure (erase a i) := by
  intro u
  by_cases hui : u = i
  · subst u
    simp [erase]
  · simpa only [erase, Function.update_of_ne hui] using ha u

theorem erase_valid (a : State L n) (ha : Valid a) (i : L) : Valid (erase a i) := by
  intro u v j hj hu hv
  have hui : u ≠ i := by intro hh; subst u; simpa [erase] using hu
  have hvi : v ≠ i := by intro hh; subst v; simpa [erase] using hv
  exact ha u v j hj (by simpa only [erase, Function.update_of_ne hui] using hu)
    (by simpa only [erase, Function.update_of_ne hvi] using hv)

theorem erase_value (a : State L n) (i : L) : erase a i i = none := Function.update_self _ _ _

theorem domain_erase (a : State L n) (i : L) : domain (erase a i) = (domain a).erase i := by
  classical
  ext u
  rw [mem_domain, Finset.mem_erase, mem_domain]
  by_cases hui : u = i
  · subst u
    simp [erase]
  · simp [erase, hui]

theorem restore (a : State L n) (i : L) (j : Fin (n+1)) (hai : a i = some j) : advance (erase a i) i j = a := by
  funext u
  by_cases hui : u = i <;> simp [advance, erase, Function.update_apply, hui, hai]

theorem edges_advance (a : State L n) (i : L) (j : Positive n) (hai : a i = none) :
    edges (advance a i j.val) = insert (i, j) (edges a) := by
  classical
  ext e
  rw [mem_edges, Finset.mem_insert, mem_edges]
  by_cases hei : e.1 = i
  · simp only [advance, hei, Function.update_self, hai, Option.some.injEq]
    constructor
    · intro hh
      exact Or.inl (Prod.ext hei (Subtype.ext hh.symm))
    · rintro (hh | hh)
      · exact congrArg (fun e : L×Positive n => e.2.val) hh.symm
      · cases hh
  · constructor
    · intro hh
      exact Or.inr (by simpa only [advance, Function.update_of_ne hei] using hh)
    · rintro (hh | hh)
      · exact (hei (congrArg Prod.fst hh)).elim
      · simpa only [advance, Function.update_of_ne hei] using hh

theorem advance_pure (a : State L n) (ha : Pure a) (i : L) (j : Positive n) : Pure (advance a i j.val) := by
  intro u
  by_cases hui : u = i
  · subst u
    simp only [advance, Function.update_self, ne_eq, Option.some.injEq]
    exact j.property
  · simpa only [advance, Function.update_of_ne hui] using ha u

theorem polynomial_pure (a : State L n) (ha : Pure a) : polynomial a = monomial (edges a) := by
  unfold polynomial
  rw [zeros_eq_empty a ha, Finset.prod_empty, mul_one]

theorem polynomial_advance (a : State L n) (ha : Pure a) (i : L) (j : Positive n) (hai : a i = none) :
    polynomial (advance a i j.val) = polynomial a*coordinate (i, j) := by
  rw [polynomial_pure _ (advance_pure a ha i j), polynomial_pure a ha, edges_advance a i j hai]
  change monomial (insert (i, j) (edges a)) = monomial (edges a)*monomial {(i, j)}
  rw [monomial_mul, Finset.union_singleton]

theorem polynomial_factor (a : State L n) (ha : Pure a) (i : L) (j : Positive n) (hai : a i = some j.val) :
    polynomial a = polynomial (erase a i)*coordinate (i, j) := by
  rw [← polynomial_advance (erase a i) (erase_pure a ha i) i j (erase_value a i), restore a i j.val hai]

theorem advance_erase (a : State L n) (i : L) (j : Fin (n+1)) : advance (erase a i) i j = advance a i j := by
  funext u
  by_cases hui : u = i <;> simp [advance, erase, Function.update_apply, hui]

theorem occupied_zero (a : State L n) (ha : Pure a) (i : L) (hai : a i = none) (j : Positive n)
    (hoccupied : ∃ u, a u = some j.val) : polynomial a*coordinate (i, j) = 0 := by
  classical
  obtain ⟨u, hu⟩ := hoccupied
  have hui : u ≠ i := by intro hh; subst u; rw [hai] at hu; cases hu
  have hnot : ¬ IsMatching (insert (i, j) (edges a)) := by
    intro hM
    have heq := hM (i, j) (Finset.mem_insert_self _ _) (u, j)
      (Finset.mem_insert_of_mem ((mem_edges a _).mpr hu)) (Or.inr rfl)
    exact hui (congrArg Prod.fst heq).symm
  rw [← polynomial_advance a ha i j hai, polynomial_pure _ (advance_pure a ha i j), edges_advance a i j hai,
    monomial_zero _ hnot]

theorem advance_valid (a : State L n) (ha : Valid a) (i : L) (j : Positive n)
    (hfree : ∀ u, a u ≠ some j.val) : Valid (advance a i j.val) := by
  apply P2MPigeonDanceStep.advance_valid a ha i 0 j.val
  exact (mem_available a 0 j.val).mpr ⟨lt_of_le_of_ne (Fin.zero_le j.val) j.property.symm, hfree⟩

theorem row_identity (p : Placements L (Positive n) → ZMod 2) (i : L) :
    p = p*equation i+∑ j : Positive n, p*coordinate (i, j) := by
  unfold equation
  rw [← Finset.mul_sum]
  ring

theorem isolate (p : Placements L (Positive n) → ZMod 2) (i : L) (j : Positive n) :
    p*coordinate (i, j) = p-p*equation i-∑ k ∈ (Finset.univ : Finset (Positive n)).erase j, p*coordinate (i, k) := by
  have hh := row_identity p i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hh
  linear_combination -hh

end ProofComplexity.P2MPigeonDanceRowErasure
end

section
-- Inlined Solutions.P2MPigeonDanceSpanningRecursion

set_option maxHeartbeats 4500000

namespace ProofComplexity.P2MPigeonDanceSpanningRecursion

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceRowErasure P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions P2MMatchingRowEquations

theorem no_dance_mem {m n : ℕ} (D : ℕ) (seed : State (Fin m) n)
    (hSpace : space (L:=Fin m) (R:=Positive n) (D-1) ≤ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (hQ : ∀ p ∈ space (L:=Fin m) (R:=Positive n) (D-1), ∀ i, p*equation i ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (hBefore : ∀ a : State (Fin m) n, Valid a → Pure a → (domain a).card ≤ D → Before a seed →
      polynomial a ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D)
    (k : ℕ) (b : State (Fin m) n) (hb : Valid b) (hPure : Pure b) (hcard : (domain b).card ≤ D)
    (hFuture : ∀ u : Fin m, k ≤ u.val → b u = seed u)
    (hBad : ∀ c, ¬ Dance (suffix m k) b c) :
    polynomial b ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D := by
  classical
  by_cases hk : k < m
  · let i : Fin m := ⟨k, hk⟩
    have hsuffix : suffix m k = i::suffix m (k+1) := suffix_cons m k hk
    cases hbi : b i with
    | none =>
      have hBad' : ∀ c, ¬ Dance (suffix m (k+1)) b c := by
        intro c hc
        apply hBad c
        rw [hsuffix]
        exact Dance.cons (Or.inl ⟨hbi, rfl⟩) hc
      exact no_dance_mem D seed hSpace hQ hBefore (k+1) b hb hPure hcard
        (fun u hu => hFuture u (by omega)) hBad'
    | some old =>
      have hold : old ≠ 0 := fun hh => hPure i (by rwa [hh] at hbi)
      let j : Positive n := ⟨old, hold⟩
      let c := erase b i
      have hcValid : Valid c := erase_valid b hb i
      have hcPure : Pure c := erase_pure b hPure i
      have hci : c i = none := erase_value b i
      have himem : i ∈ domain b := (mem_domain b i).mpr ⟨old, hbi⟩
      have hcCard : (domain c).card = (domain b).card-1 := by
        rw [domain_erase, Finset.card_erase_of_mem himem]
      have hcDegree : polynomial c ∈ space (L:=Fin m) (R:=Positive n) (D-1) := by
        apply space_mono (Nat.sub_le_sub_right hcard 1)
        simpa only [hcCard] using polynomial_mem c hcValid
      have hrow : polynomial b = polynomial c-polynomial c*equation i-
          ∑ v ∈ (Finset.univ : Finset (Positive n)).erase j, polynomial c*coordinate (i, v) :=
        (polynomial_factor b hPure i j hbi).trans (isolate (polynomial c) i j)
      rw [hrow]
      apply (P2MPigeonDanceGoodSpan.span (suffix m 0) D).sub_mem
        ((P2MPigeonDanceGoodSpan.span (suffix m 0) D).sub_mem (hSpace hcDegree) (hQ _ hcDegree i))
      apply (P2MPigeonDanceGoodSpan.span (suffix m 0) D).sum_mem
      intro v hv
      have hvj : v ≠ j := (Finset.mem_erase.mp hv).1
      by_cases hOccupied : ∃ u, c u = some v.val
      · rw [occupied_zero c hcPure i hci v hOccupied]
        exact (P2MPigeonDanceGoodSpan.span (suffix m 0) D).zero_mem
      · have hfree : ∀ u, c u ≠ some v.val := fun u hu => hOccupied ⟨u, hu⟩
        let b' := advance c i v.val
        have hEq : b' = advance b i v.val := advance_erase b i v.val
        have hb' : Valid b' := P2MPigeonDanceRowErasure.advance_valid c hcValid i v hfree
        have hPure' : Pure b' := advance_pure c hcPure i v
        have hCard' : (domain b').card ≤ D := by
          rw [hEq, advance_domain b i old v.val hbi]
          exact hcard
        have hValue : b' i = some v.val := by simp only [b', advance, Function.update_self]
        have hSeed : seed i = some old := (hFuture i (by simp [i])).symm.trans hbi
        have hAfter : ∀ u : Fin m, i < u → b' u = seed u := by
          intro u hiu
          have hui : u ≠ i := (ne_of_gt hiu)
          rw [hEq]
          simp only [advance, Function.update_of_ne hui]
          exact hFuture u (by change k < u.val at hiu; omega)
        have hne : v.val ≠ old := by
          intro hh
          exact hvj (Subtype.ext hh)
        rw [← polynomial_advance c hcPure i v hci]
        change polynomial b' ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) D
        rcases lt_trichotomy v.val old with hlt | heq | hgt
        · exact hBefore b' hb' hPure' hCard' (before_of_lower b' seed i v.val old hValue hSeed hlt hAfter)
        · exact (hne heq).elim
        · have hfreeB : ∀ u, b u ≠ some v.val := by
            intro u hu
            by_cases hui : u = i
            · subst u
              exact hne (Option.some.inj (hu.symm.trans hbi))
            · apply hfree u
              simpa only [c, erase, Function.update_of_ne hui] using hu
          have hstep : Step b i b' := Or.inr ⟨old, v.val, hbi,
            (mem_available b old v.val).mpr ⟨hgt, hfreeB⟩, hEq⟩
          have hBad' : ∀ z, ¬ Dance (suffix m (k+1)) b' z := by
            intro z hz
            apply hBad z
            rw [hsuffix]
            exact Dance.cons hstep hz
          exact no_dance_mem D seed hSpace hQ hBefore (k+1) b' hb' hPure' hCard'
            (fun u hu => hAfter u (by change k < u.val; omega)) hBad'
  · exact (hBad b (by rw [suffix_empty m k (by omega)]; exact Dance.nil b)).elim
termination_by m-k
decreasing_by all_goals omega

end ProofComplexity.P2MPigeonDanceSpanningRecursion
end

section
-- Inlined Solutions.P2MPigeonDanceMatchingStates

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceMatchingStates

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDancePolynomials P2MMatchingPolynomialFunctions

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def state (B : Placements L (Positive n)) : State L n :=
  fun u => if h : ∃ v : Positive n, (u, v) ∈ B.val then some (Classical.choose h).val else none

theorem value (B : Placements L (Positive n)) (u : L) (j : Fin (n+1)) :
    state B u = some j ↔ ∃ v : Positive n, v.val = j ∧ (u, v) ∈ B.val := by
  classical
  unfold state
  split_ifs with h
  · constructor
    · intro he
      exact ⟨Classical.choose h, Option.some.inj he, Classical.choose_spec h⟩
    · rintro ⟨v, hvj, hv⟩
      have he := B.property (u, Classical.choose h) (Classical.choose_spec h) (u, v) hv (Or.inl rfl)
      have hv' : (Classical.choose h).val = v.val := congrArg (fun e : L×Positive n => e.2.val) he
      exact congrArg Option.some (hv'.trans hvj)
  · constructor
    · intro he
      cases he
    · rintro ⟨v, _, hv⟩
      exact (h ⟨v, hv⟩).elim

theorem no_zero (B : Placements L (Positive n)) (u : L) : state B u ≠ some 0 := by
  intro hz
  obtain ⟨v, hv0, hv⟩ := (value B u 0).mp hz
  exact v.property hv0

theorem valid (B : Placements L (Positive n)) : Valid (state B) := by
  intro u v j hj hu hv
  obtain ⟨a, haj, ha⟩ := (value B u j).mp hu
  obtain ⟨b, hbj, hb⟩ := (value B v j).mp hv
  have hab : a = b := Subtype.ext (haj.trans hbj.symm)
  exact congrArg Prod.fst (B.property (u, a) ha (v, b) hb (Or.inr hab))

theorem edges (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.edges (state B) = B.val := by
  ext e
  rw [mem_edges, value]
  constructor
  · rintro ⟨v, hve, hv⟩
    have he : v = e.2 := Subtype.ext hve
    simpa only [he, Prod.mk.eta] using hv
  · intro he
    exact ⟨e.2, rfl, he⟩

theorem zeros (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.zeros (state B) = ∅ :=
  zeros_eq_empty (state B) (no_zero B)

theorem domain_card (B : Placements L (Positive n)) : (domain (state B)).card = B.val.card := by
  have hh := P2MPigeonDancePolynomials.domain_card (state B)
  rw [edges, zeros, Finset.card_empty, add_zero] at hh
  exact hh.symm

theorem polynomial (B : Placements L (Positive n)) : P2MPigeonDancePolynomials.polynomial (state B) = monomial B.val := by
  unfold P2MPigeonDancePolynomials.polynomial
  rw [edges, zeros, Finset.prod_empty, mul_one]

end ProofComplexity.P2MPigeonDanceMatchingStates
end

section
-- Inlined Solutions.P2MPigeonDanceSpanning

set_option maxHeartbeats 4000000

namespace ProofComplexity.P2MPigeonDanceSpanning

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceRowErasure P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions P2MPigeonDanceCounting

theorem none_dance {L : Type} [Fintype L] [DecidableEq L] {n : ℕ} (is : List L) (a : State L n)
    (ha : ∀ u, a u = none) : Dance is a a := by
  induction is with
  | nil => exact Dance.nil _
  | cons i is ih => exact Dance.cons (Or.inl ⟨ha i, rfl⟩) ih

theorem one_mem {L : Type} [Fintype L] [DecidableEq L] {n : ℕ} (is : List L) (d : ℕ) :
    (1 : Placements L (Positive n) → ZMod 2) ∈ P2MPigeonDanceGoodSpan.span is d := by
  classical
  let a : State L n := fun _ => none
  have hValid : Valid a := by simp [Valid, a]
  have hDomain : domain a = ∅ := by ext u; simp [mem_domain, a]
  have hEdges : edges a = ∅ := by ext e; simp [mem_edges, a]
  have hZeros : zeros a = ∅ := zeros_eq_empty a (by intro u; simp [a])
  let a' : GoodState (n:=n) is d := ⟨a, hValid, by rw [hDomain]; simp, ⟨a, none_dance is a (fun _ => rfl)⟩⟩
  have hPoly : polynomial a = 1 := by
    unfold polynomial
    rw [hEdges, hZeros, Finset.prod_empty, mul_one, monomial_empty]
  rw [← hPoly]
  exact P2MPigeonDanceGoodSpan.basis_mem is d a'

/-- The successful mixed-state polynomials span all partial-matching
polynomials through degree d, provided 2d does not exceed the number of holes. -/
theorem span_eq_space (m n d : ℕ) (hbudget : 2*d ≤ n) :
    P2MPigeonDanceGoodSpan.span (n:=n) (suffix m 0) d = space (L:=Fin m) (R:=Positive n) d := by
  classical
  induction d with
  | zero =>
    apply le_antisymm (P2MPigeonDanceGoodSpan.span_le_degree _ _) _
    apply Submodule.span_le.mpr
    rintro p ⟨A, hA, hCard, rfl⟩
    have hEmpty : A = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hEmpty, monomial_empty]
    exact one_mem (suffix m 0) 0
  | succ d ih =>
    have hIH := ih (by omega : 2*d ≤ n)
    have hSpace : space (L:=Fin m) (R:=Positive n) d ≤ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      rw [← hIH]
      exact P2MPigeonDanceGoodSpan.span_mono _ (Nat.le_succ d)
    have hQ : ∀ p ∈ space (L:=Fin m) (R:=Positive n) d, ∀ i,
        p*P2MMatchingRowEquations.equation i ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      intro p hp i
      have hp' : p ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) d := by rwa [hIH]
      exact P2MPigeonDanceGoodSpan.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
        (d+1) (by omega) hbudget i p (by simpa only [Nat.add_sub_cancel] using hp')
    have hState : ∀ a : State (Fin m) n, Valid a → Pure a → (domain a).card ≤ d+1 →
        polynomial a ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1) := by
      intro a
      refine (before_wellFounded m n).induction (C := fun b => Valid b → Pure b →
        (domain b).card ≤ d+1 → polynomial b ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d+1)) a ?_
      intro b ihb hb hPure hCard
      by_cases hDance : ∃ c, Dance (suffix m 0) b c
      · exact P2MPigeonDanceGoodSpan.basis_mem _ _ ⟨b, hb, hCard, hDance⟩
      · exact P2MPigeonDanceSpanningRecursion.no_dance_mem (d+1) b hSpace hQ
          (fun c hc hcp hcc hbefore => ihb c hbefore hc hcp hcc)
          0 b hb hPure hCard (fun _ _ => rfl) (fun c hc => hDance ⟨c, hc⟩)
    apply le_antisymm (P2MPigeonDanceGoodSpan.span_le_degree _ _) _
    apply Submodule.span_le.mpr
    rintro p ⟨A, hA, hCard, rfl⟩
    let B : Placements (Fin m) (Positive n) := ⟨A, hA⟩
    have hRoot := hState (P2MPigeonDanceMatchingStates.state B) (P2MPigeonDanceMatchingStates.valid B)
      (P2MPigeonDanceMatchingStates.no_zero B) (by rw [P2MPigeonDanceMatchingStates.domain_card]; exact hCard)
    rw [P2MPigeonDanceMatchingStates.polynomial] at hRoot
    exact hRoot

end ProofComplexity.P2MPigeonDanceSpanning
end

section
-- Inlined Solutions.P2MPigeonDanceBasis

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDanceBasis

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MPigeonDanceFiniteOrder P2MMatchingPolynomialFunctions

theorem independent (m n d : ℕ) (hbudget : 2*d ≤ n) :
    LinearIndependent (ZMod 2)
      (fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) := by
  classical
  apply linearIndependent_iff_card_le_finrank_span.mpr
  change Fintype.card (GoodState (n:=n) (suffix m 0) d) ≤
    Module.finrank (ZMod 2) (P2MPigeonDanceGoodSpan.span (suffix m 0) d)
  rw [P2MPigeonDanceSpanning.span_eq_space m n d hbudget]
  simpa only [Nat.card_eq_fintype_card] using
    count_le_dimension (n:=n) (suffix m 0) (suffix_nodup m 0) (suffix_covers m) d

/-- Intersecting spans of subfamilies of an independent family intersects
the indexing sets. This is the degree-filtration step in the dance argument. -/
theorem span_image_inter {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    {v : I → V} (hv : LinearIndependent K v) (s t : Set I) :
    Submodule.span K (v '' (s ∩ t)) =
      Submodule.span K (v '' s) ⊓ Submodule.span K (v '' t) := by
  apply le_antisymm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))
  · intro p hp
    obtain ⟨f, hf, hfp⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hp.1
    obtain ⟨g, hg, hgp⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hp.2
    have hfg : f = g := hv (hfp.trans hgp.symm)
    apply (Finsupp.mem_span_image_iff_linearCombination K).mpr
    refine ⟨f, ?_, hfp⟩
    intro i hi
    exact ⟨hf hi, hg (by simpa only [← hfg] using hi)⟩

end ProofComplexity.P2MPigeonDanceBasis
end

section
-- Inlined Solutions.P2MPigeonDanceEraseDance

set_option maxHeartbeats 2500000

namespace ProofComplexity.P2MPigeonDanceEraseDance

open P2MPigeonDanceStep P2MPigeonDanceRelation P2MPigeonDanceRowErasure P2MPigeonDancePolynomials

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem erase_advance (a : State L n) (i k : L) (j : Fin (n+1)) (hki : k ≠ i) :
    erase (advance a k j) i = advance (erase a i) k j := by
  funext u
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    simp_all [erase, advance, Function.update_apply]

theorem erase_advance_self (a : State L n) (i : L) (j : Fin (n+1)) :
    erase (advance a i j) i = erase a i := by
  funext u
  by_cases hui : u = i <;> simp [erase, advance, Function.update_apply, hui]

theorem step (a b : State L n) (k i : L) (h : Step a k b) :
    Step (erase a i) k (erase b i) := by
  rcases h with ⟨hak, rfl⟩ | ⟨old, new, hak, hnew, rfl⟩
  · left
    refine ⟨?_, rfl⟩
    by_cases hki : k = i <;> simp [erase, Function.update_apply, hki, hak]
  · by_cases hki : k = i
    · subst k
      exact Or.inl ⟨erase_value a i, erase_advance_self a i new⟩
    · right
      refine ⟨old, new, ?_, ?_, erase_advance a i k new hki⟩
      · simpa only [erase, Function.update_of_ne hki] using hak
      · apply (mem_available _ _ _).mpr
        obtain ⟨hlt, hfree⟩ := (mem_available a old new).mp hnew
        refine ⟨hlt, ?_⟩
        intro u hu
        by_cases hui : u = i
        · subst u
          simpa [erase] using hu
        · exact hfree u (by simpa only [erase, Function.update_of_ne hui] using hu)

theorem dance {is : List L} {a b : State L n} (h : Dance is a b) (i : L) :
    Dance is (erase a i) (erase b i) := by
  induction h with
  | nil => exact Dance.nil _
  | cons hs hr ih => exact Dance.cons (step _ _ _ i hs) ih

theorem polynomial_factor_zero (a : State L n) (i : L) (hai : a i = some 0) :
    polynomial a = polynomial (erase a i)*P2MMatchingRowEquations.equation i := by
  rw [← P2MPigeonDanceInsertZero.polynomial (erase a i) i (erase_value a i), restore a i 0 hai]

end ProofComplexity.P2MPigeonDanceEraseDance
end

section
-- Inlined Solutions.P2MPigeonDanceConsequences

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MPigeonDanceConsequences

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

noncomputable def span (is : List L) (d : ℕ) : Submodule (ZMod 2) (Placements L (Positive n) → ZMod 2) :=
  Submodule.span (ZMod 2)
    ((fun a : GoodState (n:=n) is d => polynomial a.val) '' {a | (zeros a.val).Nonempty})

theorem basis_mem (is : List L) (d : ℕ) (a : GoodState (n:=n) is d) (ha : (zeros a.val).Nonempty) :
    polynomial a.val ∈ span is d := Submodule.subset_span ⟨a, ha, rfl⟩

theorem span_le_good (is : List L) (d : ℕ) : span (n:=n) is d ≤ P2MPigeonDanceGoodSpan.span is d := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, ha, rfl⟩
  exact P2MPigeonDanceGoodSpan.basis_mem is d a

theorem span_mono (is : List L) {d e : ℕ} (hde : d ≤ e) : span (n:=n) is d ≤ span is e := by
  apply Submodule.span_le.mpr
  rintro p ⟨a, ha, rfl⟩
  exact basis_mem is e ⟨a.val, a.property.1, a.property.2.1.trans hde, a.property.2.2⟩ ha

theorem mul_equation (is : List L) (hnd : is.Nodup) (hcovers : ∀ u, u ∈ is)
    (d : ℕ) (hd : 1 ≤ d) (hbudget : 2*d ≤ n) (i : L)
    (p : Placements L (Positive n) → ZMod 2) (hp : p ∈ P2MPigeonDanceGoodSpan.span is (d-1)) :
    p*equation i ∈ span is d := by
  classical
  have hle : P2MPigeonDanceGoodSpan.span (n:=n) is (d-1) ≤
      (span is d).comap (LinearMap.mulRight (ZMod 2) (equation i)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, rfl⟩
    change polynomial a.val*equation i ∈ span is d
    cases hai : a.val i with
    | none =>
      have hcard : (domain (advance a.val i 0)).card = (domain a.val).card+1 := by
        have hh := domain_card (advance a.val i 0)
        rw [P2MPigeonDanceInsertZero.edges a.val i hai, P2MPigeonDanceInsertZero.zeros,
          Finset.card_insert_of_notMem (P2MPigeonDanceInsertZero.not_mem_zeros a.val i hai)] at hh
        have hh' := domain_card a.val
        omega
      obtain ⟨b, hDance⟩ := a.property.2.2
      have hsmall : 2*((domain a.val).card+1) ≤ n := by
        have hh := a.property.2.1
        omega
      obtain ⟨c, hc⟩ := P2MPigeonDanceUnusedHole.insert_zero is hnd a.val b i (hcovers i) hai hsmall hDance
      let a' : GoodState (n:=n) is d := ⟨advance a.val i 0,
        P2MPigeonDanceInsertZero.valid a.val a.property.1 i,
        by rw [hcard]; have hh := a.property.2.1; omega, ⟨c, hc⟩⟩
      rw [← P2MPigeonDanceInsertZero.polynomial a.val i hai]
      exact basis_mem is d a' ⟨i, (mem_zeros _ _).mpr (Function.update_self _ _ _)⟩
    | some j =>
      by_cases hj : j = 0
      · have hai0 : a.val i = some 0 := by rwa [hj] at hai
        rw [P2MPigeonDanceRowMultiplication.zero_self a.val i hai0]
        exact span_mono is (Nat.sub_le d 1)
          (basis_mem is (d-1) a ⟨i, (mem_zeros _ _).mpr hai0⟩)
      · rw [P2MPigeonDanceRowMultiplication.positive_zero a.val i j hj hai]
        exact (span is d).zero_mem
  exact hle hp

noncomputable def emptyGood (m n d : ℕ) : GoodState (n:=n) (suffix m 0) d := by
  classical
  let a : State (Fin m) n := fun _ => none
  have hvalid : Valid a := by simp [a, Valid]
  have hdom : domain a = ∅ := by ext u; simp [mem_domain, a]
  exact ⟨a, hvalid, by rw [hdom]; simp,
    ⟨a, P2MPigeonDanceSpanning.none_dance _ a (fun _ => rfl)⟩⟩

theorem emptyGood_polynomial (m n d : ℕ) : polynomial (emptyGood m n d).val = 1 := by
  classical
  have he : edges (emptyGood m n d).val = ∅ := by ext e; simp [mem_edges, emptyGood]
  have hz : zeros (emptyGood m n d).val = ∅ := by ext u; simp [mem_zeros, emptyGood]
  rw [polynomial, he, hz, Finset.prod_empty, mul_one, monomial_empty]

theorem one_not_mem (m n d : ℕ) (hbudget : 2*d ≤ n) :
    (1 : Placements (Fin m) (Positive n) → ZMod 2) ∉ span (suffix m 0) d := by
  classical
  rw [← emptyGood_polynomial m n d]
  apply (P2MPigeonDanceBasis.independent m n d hbudget).notMem_span_image
  change ¬ (zeros (emptyGood m n d).val).Nonempty
  simp [zeros, emptyGood]

end ProofComplexity.P2MPigeonDanceConsequences
end

section
-- Inlined Solutions.P2MBitPHPMatchingAxioms

set_option maxHeartbeats 4000000

namespace ProofComplexity.P2MBitPHPMatchingAxioms

open MvPolynomial P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials
open P2MPigeonDanceFiniteOrder SemAC02.Supplement P2MBitPHPMatchingDecoding

variable {m n ℓ : ℕ}

theorem delta_value (u : Fin m) (a : Fin ℓ → Bool) (x : Fin m × Fin ℓ → Bool) :
    polyFn (deltaA u a) x = if (fun t => x (u,t)) = a then 1 else 0 := by
  classical
  unfold polyFn deltaA
  rw [map_prod]
  by_cases h : (fun t => x (u,t)) = a
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro t ht
    have he : x (u,t) = a t := congrFun h t
    cases ha : a t <;> simp [ha, boolPt, he]
  · rw [if_neg h]
    obtain ⟨t, ht⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    cases ha : a t <;> cases hx : x (u,t) <;> simp_all [boolPt]

theorem delta_decoded (addr : Positive n ≃ (Fin ℓ → Bool)) (u : Fin m) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a) (decoded addr B)) =
      coordinate (u,addr.symm a)+(if a = (fun _ => false) then 1 else 0 : ZMod 2) • equation u := by
  classical
  funext B
  by_cases hu : ∃ j, (u,j) ∈ B.val
  · obtain ⟨j,hj⟩ := hu
    have hrow : (fun t => decoded addr B (u,t)) = addr j := funext (decoded_occupied addr B u j hj)
    have htarget : (u,addr.symm a) ∈ B.val ↔ addr j = a := by
      constructor
      · intro h
        have hj' : j = addr.symm a := congrArg Prod.snd (B.property (u,j) hj (u,addr.symm a) h (Or.inl rfl))
        rw [hj', addr.apply_symm_apply]
      · intro h
        have hj' : j = addr.symm a := addr.injective (h.trans (addr.apply_symm_apply a).symm)
        simpa only [← hj'] using hj
    simp only [delta_value, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      coordinate_value, equation_value, if_pos (show ∃ j, (u,j) ∈ B.val from ⟨j,hj⟩),
      mul_zero, add_zero]
    by_cases hja : addr j = a
    · simp only [if_pos hja, if_pos (htarget.mpr hja)]
    · simp only [if_neg hja, if_neg (mt htarget.mp hja)]
  · have hrow : (fun t => decoded addr B (u,t)) = (fun _ => false) :=
      funext (decoded_absent addr B u hu)
    have htarget : (u,addr.symm a) ∉ B.val := fun h => hu ⟨_,h⟩
    simp only [delta_value, hrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      coordinate_value, if_neg htarget, equation_value, if_neg hu, mul_one, zero_add]
    simp only [eq_comm]

theorem delta_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (u : Fin m) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a) (decoded addr B)) ∈ space 1 := by
  rw [delta_decoded]
  exact (space 1).add_mem (coordinate_mem _) ((space 1).smul_mem _ (equation_mem _))

theorem collision_zero (u v : Fin m) (huv : u ≠ v) (j : Positive n) :
    coordinate (u,j)*coordinate (v,j) = 0 := by
  have hbad : ¬ IsMatching ({(u,j)} ∪ {(v,j)}) := by
    intro h
    have he := h (u,j) (by simp) (v,j) (by simp) (Or.inr rfl)
    exact huv (congrArg Prod.fst he)
  exact (monomial_mul {(u,j)} {(v,j)}).trans (monomial_zero _ hbad)

theorem axiom_mem (addr : Positive n ≃ (Fin ℓ → Bool)) (d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (u v : Fin m) (huv : u ≠ v) (a : Fin ℓ → Bool) :
    (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) ∈
      P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  let c : ZMod 2 := if a = (fun _ => false) then 1 else 0
  let du : Placements (Fin m) (Positive n) → ZMod 2 := fun B => polyFn (deltaA u a) (decoded addr B)
  let dv : Placements (Fin m) (Positive n) → ZMod 2 := fun B => polyFn (deltaA v a) (decoded addr B)
  let xu := coordinate (u,addr.symm a)
  let xv := coordinate (v,addr.symm a)
  have hdu : du = xu+c • equation u := delta_decoded addr u a
  have hdv : dv = xv+c • equation v := delta_decoded addr v a
  have hx : xu*xv = 0 := collision_zero u v huv _
  have hid : du*dv = c • (dv*equation u+xu*equation v) := by
    rw [hdu, hdv]
    simp only [Algebra.smul_def]
    linear_combination hx
  have hvGood : dv ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
    rw [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    exact space_mono (by omega : 1 ≤ d-1) (delta_mem addr v a)
  have hxGood : xu ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
    rw [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    exact space_mono (by omega : 1 ≤ d-1) (coordinate_mem _)
  have hQu := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
    d (by omega) hbudget u dv hvGood
  have hQv := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
    d (by omega) hbudget v xu hxGood
  have hout := (P2MPigeonDanceConsequences.span (suffix m 0) d).smul_mem c
    ((P2MPigeonDanceConsequences.span (suffix m 0) d).add_mem hQu hQv)
  rw [← hid] at hout
  have he : (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) = du*dv := by
    funext B
    exact map_mul (eval (boolPt (decoded addr B))) _ _
  rwa [he]

end ProofComplexity.P2MBitPHPMatchingAxioms
end

section
-- Inlined Solutions.P2MPigeonDanceDegreeFiltration

set_option maxHeartbeats 3000000

namespace ProofComplexity.P2MPigeonDanceDegreeFiltration

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder

variable {L : Type} [Fintype L] [DecidableEq L] {n : ℕ}

theorem good_span_cut (is : List L) (d e : ℕ) (hed : e ≤ d) :
    P2MPigeonDanceGoodSpan.span (n:=n) is e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) is d => polynomial a.val) '' {a | (domain a.val).card ≤ e}) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, a.property.1, a.property.2.1.trans hed, a.property.2.2⟩, a.property.2.1, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.val, a.property.1, ha, a.property.2.2⟩, rfl⟩

theorem consequence_span_cut (is : List L) (d e : ℕ) (hed : e ≤ d) :
    P2MPigeonDanceConsequences.span (n:=n) is e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) is d => polynomial a.val) ''
        {a | (zeros a.val).Nonempty ∧ (domain a.val).card ≤ e}) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a.val, a.property.1, a.property.2.1.trans hed, a.property.2.2⟩, ⟨ha, a.property.2.1⟩, rfl⟩
  · rintro ⟨a, ⟨ha, he⟩, rfl⟩
    exact ⟨⟨a.val, a.property.1, he, a.property.2.2⟩, ha, rfl⟩

theorem degree_cut (m n d e : ℕ) (hbudget : 2*d ≤ n) (hed : e ≤ d)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (hdegree : p ∈ space e) : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) e := by
  have he : 2*e ≤ n := by omega
  have hlow : space (L:=Fin m) (R:=Positive n) e = Submodule.span (ZMod 2)
      ((fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) ''
        {a | (domain a.val).card ≤ e}) := by
    rw [← P2MPigeonDanceSpanning.span_eq_space m n e he]
    exact good_span_cut _ d e hed
  rw [consequence_span_cut _ d e hed]
  have hIntersection := P2MPigeonDanceBasis.span_image_inter
    (P2MPigeonDanceBasis.independent m n d hbudget)
    {a | (zeros a.val).Nonempty} {a | (domain a.val).card ≤ e}
  change p ∈ Submodule.span (ZMod 2)
    ((fun a : GoodState (n:=n) (suffix m 0) d => polynomial a.val) ''
      ({a | (zeros a.val).Nonempty} ∩ {a | (domain a.val).card ≤ e}))
  rw [hIntersection]
  exact ⟨hp, by rwa [← hlow]⟩

end ProofComplexity.P2MPigeonDanceDegreeFiltration
end

section
-- Inlined Solutions.P2MPigeonDanceWeakClosure

set_option maxHeartbeats 3500000

namespace ProofComplexity.P2MPigeonDanceWeakClosure

open P2MPigeonDanceStep P2MPigeonDanceDomain P2MPigeonDanceRelation P2MPigeonDancePolynomials
open P2MPigeonDanceCounting P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDanceFiniteOrder
open P2MPigeonDanceRowErasure

theorem coordinate (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (hdegree : p ∈ space (d-1)) (e : Fin m × Positive n) :
    p*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  have hp' := P2MPigeonDanceDegreeFiltration.degree_cut m n d (d-1) hbudget (Nat.sub_le d 1) p hp hdegree
  have hle : P2MPigeonDanceConsequences.span (n:=n) (suffix m 0) (d-1) ≤
      (P2MPigeonDanceConsequences.span (suffix m 0) d).comap
        (LinearMap.mulRight (ZMod 2) (P2MMatchingRowEquations.coordinate e)) := by
    apply Submodule.span_le.mpr
    rintro q ⟨a, ha, rfl⟩
    change polynomial a.val*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceConsequences.span (suffix m 0) d
    obtain ⟨i, hi⟩ := ha
    have hai : a.val i = some 0 := (mem_zeros _ _).mp hi
    let c := erase a.val i
    have hcValid : Valid c := erase_valid a.val a.property.1 i
    have hiDomain : i ∈ domain a.val := (mem_domain _ _).mpr ⟨0, hai⟩
    have hcCard : (domain c).card ≤ d-2 := by
      have hh := a.property.2.1
      change (domain (erase a.val i)).card ≤ d-2
      rw [domain_erase, Finset.card_erase_of_mem hiDomain]
      omega
    have hcDegree : polynomial c ∈ space (d-2) := space_mono hcCard (polynomial_mem c hcValid)
    have hProduct : polynomial c*P2MMatchingRowEquations.coordinate e ∈ space (d-1) := by
      apply space_mono (show d-2+1 ≤ d-1 by omega)
      exact mul_mem hcDegree (coordinate_mem e)
    have hGood : polynomial c*P2MMatchingRowEquations.coordinate e ∈ P2MPigeonDanceGoodSpan.span (suffix m 0) (d-1) := by
      rwa [P2MPigeonDanceSpanning.span_eq_space m n (d-1) (by omega)]
    have hOut := P2MPigeonDanceConsequences.mul_equation (suffix m 0) (suffix_nodup m 0) (suffix_covers m)
      d (by omega) hbudget i _ hGood
    rw [P2MPigeonDanceEraseDance.polynomial_factor_zero a.val i hai]
    convert hOut using 1 <;> ring
  exact hle hp'

theorem monomial (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (e : ℕ) (hdegree : p ∈ space e) (A : Finset (Fin m × Positive n))
    (hA : IsMatching A) (hbound : e+A.card ≤ d) :
    p*P2MMatchingPolynomialFunctions.monomial A ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [monomial_empty, mul_one] using hp
  | @insert x A hx ih =>
    have hAM : IsMatching A := matching_mono (Finset.subset_insert _ _) hA
    have hcard : (insert x A).card = A.card+1 := Finset.card_insert_of_notMem hx
    have hmem := ih hAM (by rw [hcard] at hbound; omega)
    have hdeg : p*P2MMatchingPolynomialFunctions.monomial A ∈ space (d-1) := by
      apply space_mono (show e+A.card ≤ d-1 by rw [hcard] at hbound; omega)
      exact mul_mem hdegree (monomial_mem A hAM A.card le_rfl)
    have hout := coordinate m n d hd hbudget _ hmem hdeg x
    have hX : P2MMatchingRowEquations.coordinate x = P2MMatchingPolynomialFunctions.monomial {x} := rfl
    rw [hX, mul_assoc, monomial_mul, Finset.union_singleton] at hout
    exact hout

theorem mul (m n d : ℕ) (hd : 2 ≤ d) (hbudget : 2*d ≤ n)
    (p q : Placements (Fin m) (Positive n) → ZMod 2)
    (hp : p ∈ P2MPigeonDanceConsequences.span (suffix m 0) d)
    (e f : ℕ) (hdegree : p ∈ space e) (hq : q ∈ space f) (hbound : e+f ≤ d) :
    p*q ∈ P2MPigeonDanceConsequences.span (suffix m 0) d := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨A, hA, hcard, rfl⟩ := hq
    exact monomial m n d hd hbudget p hp e hdegree A hA (by omega)
  | zero => simpa only [mul_zero] using (P2MPigeonDanceConsequences.span (suffix m 0) d).zero_mem
  | add q r hq hr ihq ihr =>
    simpa only [mul_add] using (P2MPigeonDanceConsequences.span (suffix m 0) d).add_mem ihq ihr
  | smul c q hq ih =>
    simpa only [mul_smul_comm] using (P2MPigeonDanceConsequences.span (suffix m 0) d).smul_mem c ih

end ProofComplexity.P2MPigeonDanceWeakClosure
end

section
-- Inlined Solutions.P2MBitPHPSemanticObstruction

set_option maxHeartbeats 4000000

namespace ProofComplexity.P2MBitPHPSemanticObstruction

open P2MMatchingPolynomialFunctions P2MMatchingRowEquations P2MPigeonDancePolynomials P2MPigeonDanceFiniteOrder
open SemAC02.Supplement P2MBitPHPMatchingDecoding

theorem semantic_step (m n ℓ D K : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hK : 2 ≤ K) (hbudget : 2*K ≤ n) (hDK : 3*D ≤ K)
    (f g h : ACirc (ZMod 2) (Fin m × Fin ℓ))
    (hfD : fnDeg (cval f) ≤ D) (hgD : fnDeg (cval g) ≤ D) (hhD : fnDeg (cval h) ≤ D)
    (hf : (fun B => cval f (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K)
    (hg : (fun B => cval g (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K)
    (hsem : ∀ x : Fin m × Fin ℓ → Bool, cval f x = 0 → cval g x = 0 → cval h x = 0) :
    (fun B => cval h (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
  let F : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval f (decoded addr B)
  let G : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval g (decoded addr B)
  let H : Placements (Fin m) (Positive n) → ZMod 2 := fun B => cval h (decoded addr B)
  have hF : F ∈ space D := space_mono hfD (circuit_mem addr f)
  have hG : G ∈ space D := space_mono hgD (circuit_mem addr g)
  have hH : H ∈ space D := space_mono hhD (circuit_mem addr h)
  have hOneG : 1+G ∈ space D := (space D).add_mem (one_mem D) hG
  have hCoeff : H*(1+G) ∈ space (2*D) := by
    simpa only [two_mul] using mul_mem hH hOneG
  have hProd1 := P2MPigeonDanceWeakClosure.mul m n K hK hbudget F (H*(1+G)) hf D (2*D) hF hCoeff (by omega)
  have hProd2 := P2MPigeonDanceWeakClosure.mul m n K hK hbudget G H hg D D hG hH (by omega)
  have hid : H = F*(H*(1+G))+G*H := by
    funext B
    change H B = F B*(H B*(1+G B))+G B*H B
    rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (F B) with hF | hF <;>
      rcases AC02Frege.P2MMajorityFoundation.eq_zero_or_one (G B) with hG | hG
    · have hH : H B = 0 := hsem (decoded addr B) hF hG
      simp [hF, hG, hH]
    all_goals simp [hF, hG, CharTwo.add_self_eq_zero]
  change H ∈ P2MPigeonDanceConsequences.span (suffix m 0) K
  rw [hid]
  exact (P2MPigeonDanceConsequences.span (suffix m 0) K).add_mem hProd1 hProd2

theorem no_refutation (m n ℓ D : ℕ) (addr : Positive n ≃ (Fin ℓ → Bool))
    (hn : 4 ≤ n) (hdegree : 6*D ≤ n)
    (π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)))
    (hπ : IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π)
    (hD : ∀ c ∈ π, fnDeg (cval c) ≤ D) : False := by
  classical
  let K := max 2 (3*D)
  have hK : 2 ≤ K := le_max_left _ _
  have hDK : 3*D ≤ K := le_max_right _ _
  have hbudget : 2*K ≤ n := by dsimp [K]; omega
  have hall : ∀ k (hk : k < π.length),
      (fun B => cval π[k] (decoded addr B)) ∈ P2MPigeonDanceConsequences.span (suffix m 0) K := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      rcases hπ.2.1 k hk with ha | hz | hs
      · obtain ⟨a, ha, he⟩ := ha
        obtain ⟨p, hp, rfl⟩ := ha
        obtain ⟨u,v,a,huv,rfl⟩ := hp
        have hEq : (fun B => cval π[k] (decoded addr B)) =
            (fun B => polyFn (deltaA u a*deltaA v a) (decoded addr B)) := by
          funext B
          exact he _ (Set.mem_univ _)
        rw [hEq]
        exact P2MBitPHPMatchingAxioms.axiom_mem addr K hK hbudget u v huv a
      · have hEq : (fun B => cval π[k] (decoded addr B)) = 0 := by
          funext B
          exact hz _ (Set.mem_univ _)
        rw [hEq]
        exact (P2MPigeonDanceConsequences.span (suffix m 0) K).zero_mem
      · obtain ⟨i,j,hi,hj,hs⟩ := hs
        exact semantic_step m n ℓ D K addr hK hbudget hDK π[i] π[j] π[k]
          (hD _ (List.getElem_mem (hi.trans hk))) (hD _ (List.getElem_mem (hj.trans hk)))
          (hD _ (List.getElem_mem hk)) (ih i hi (hi.trans hk)) (ih j hj (hj.trans hk))
          (fun x => hs x (Set.mem_univ x))
  obtain ⟨c,hLast,hOne⟩ := hπ.2.2
  have hc : c ∈ π := List.mem_of_getLast? hLast
  obtain ⟨k,hk,hck⟩ := List.mem_iff_getElem.mp hc
  have hOut := hall k hk
  have hEq : (fun B => cval π[k] (decoded addr B)) = 1 := by
    funext B
    rw [hck]
    exact hOne _ (Set.mem_univ _)
  rw [hEq] at hOut
  exact P2MPigeonDanceConsequences.one_not_mem m n K hbudget hOut

end ProofComplexity.P2MBitPHPSemanticObstruction
end

section
-- Inlined Solutions.P2MBitPHPDegreeLowerBound

set_option maxHeartbeats 4000000

namespace SemAC02.Supplement.P2MBitPHPDegreeLowerBound

open ProofComplexity ProofComplexity.P2MPigeonDancePolynomials

noncomputable def addresses (ℓ : ℕ) : Positive (2^ℓ) ≃ (Fin ℓ → Bool) :=
  Fintype.equivOfCardEq (by rw [P2MPigeonDanceUnusedHole.positive_card]; simp)

theorem full :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π →
        ∃ c ∈ π, ((2 : ℝ) ^ ℓ) / 6 ≤ (fnDeg (cval c) : ℝ) := by
  classical
  refine ⟨2, ?_⟩
  intro ℓ hℓ m hm π hπ
  by_contra h
  push_neg at h
  obtain ⟨c,hLast,hOne⟩ := hπ.2.2
  have hc : c ∈ π := List.mem_of_getLast? hLast
  let D := π.toFinset.sup (fun c => fnDeg (cval c))
  have hD : ∀ c ∈ π, fnDeg (cval c) ≤ D := by
    intro c hc
    exact Finset.le_sup (f:=fun c => fnDeg (cval c)) (List.mem_toFinset.mpr hc)
  have hnonempty : π.toFinset.Nonempty := ⟨c,List.mem_toFinset.mpr hc⟩
  obtain ⟨c',hc',hDc⟩ := Finset.exists_mem_eq_sup π.toFinset hnonempty (fun c => fnDeg (cval c))
  have hReal : (D : ℝ) < (2:ℝ)^ℓ/6 := by
    change ((π.toFinset.sup (fun c => fnDeg (cval c)) : ℕ) : ℝ) < _
    rw [hDc]
    exact h c' (List.mem_toFinset.mp hc')
  have hbudget : 6*D ≤ 2^ℓ := by
    have hh : (6:ℝ)*D < (2:ℝ)^ℓ := by linarith
    have hhNat : 6*D < 2^ℓ := by exact_mod_cast hh
    omega
  have hn : 4 ≤ 2^ℓ := calc
    4 = 2^2 := by norm_num
    _ ≤ 2^ℓ := Nat.pow_le_pow_right (by omega) hℓ
  exact P2MBitPHPSemanticObstruction.no_refutation m (2^ℓ) ℓ D (addresses ℓ) hn hbudget π hπ hD

end SemAC02.Supplement.P2MBitPHPDegreeLowerBound
end

end P2MBitPHPProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ m : ℕ, 2 ^ ℓ < m →
      ∀ π : List (ACirc (ZMod 2) (Fin m × Fin ℓ)),
        IsSemPCRef (fun _ => True) Set.univ (polyAx (bphp m ℓ)) π →
        ∃ c ∈ π, ((2 : ℝ) ^ ℓ) / 6 ≤ (fnDeg (cval c) : ℝ)  := by
  exact P2MBitPHPProof.SemAC02.Supplement.P2MBitPHPDegreeLowerBound.full
