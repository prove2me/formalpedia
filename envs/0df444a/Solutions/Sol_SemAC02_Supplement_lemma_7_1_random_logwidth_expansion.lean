-- Prove2me | solution 1 for SemAC02.Supplement.lemma_7_1_random_logwidth_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T10:11:59.143787+00:00
-- url     : https://prove2.me/submissions/dc0264a1-cd7a-4db8-a2e7-e08d5a504106

import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Ble
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Supplement_randCNF
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_SemAC02_Supplement_IsSemPCRef

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MRandomLogExpansionProof
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
-- Inlined Solutions.P2MCNFExpansionPolynomials

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MCNFExpansionPolynomials

open MvPolynomial LiftSAParity AC02Frege AC02Frege.P2MBooleanAlgebra

attribute [local instance] Classical.propDecidable

noncomputable def polynomial {V : Type} (C : Clause V) : MvPolynomial V (ZMod 2) :=
  ML (clausePolyF C)

theorem multilinear {V : Type} (C : Clause V) : IsMultilinear (polynomial C) := ml_multilinear _

theorem value {V : Type} (C : Clause V) (x : V → Bool) :
    eval (toF2 x) (polynomial C)=if Falsifies x C then 1 else 0 := by
  rw [polynomial,eval_ml]
  change eval (toF2 x) (∏ l∈C, litPolyF l)=_
  rw [map_prod]
  have hlit (l : V×Bool) : eval (toF2 x) (litPolyF (F:=ZMod 2) l)=if x l.1=l.2 then 0 else 1 := by
    cases hb : l.2 <;> cases hx : x l.1 <;> simp [litPolyF,toF2,hb,hx]
  by_cases hf : Falsifies x C
  · rw [if_pos hf]
    exact Finset.prod_eq_one (fun l hl => (hlit l).trans (if_neg (hf l hl)))
  · rw [if_neg hf]
    unfold Falsifies at hf
    push_neg at hf
    obtain ⟨l,hl,he⟩ := hf
    exact Finset.prod_eq_zero hl ((hlit l).trans (if_pos he))

theorem degree {V : Type} (C : Clause V) : (polynomial C).totalDegree ≤ C.card := by
  apply (AC02Frege.P2MBooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_finsetProd C _).trans
  calc
    (∑ l∈C, (litPolyF (F:=ZMod 2) l).totalDegree) ≤ ∑ _l∈C, 1 := by
      apply Finset.sum_le_sum
      intro l hl
      unfold litPolyF
      split_ifs
      · exact (totalDegree_sub _ _).trans (by simp)
      · simp
    _ = C.card := by simp

theorem vars_subset {V : Type} [DecidableEq V] (C : Clause V) :
    (polynomial C).vars⊆C.image Prod.fst := by
  intro x hx
  have hraw := AC02Frege.P2MBooleanRestrictions.ml_vars_subset (clausePolyF (F:=ZMod 2) C) hx
  obtain ⟨l,hl,hxl⟩ := Finset.mem_biUnion.mp (vars_prod _ hraw)
  have hf : (litPolyF (F:=ZMod 2) l).vars⊆{l.1} := by
    unfold litPolyF
    split_ifs
    · simpa using vars_sub_subset (1 : MvPolynomial V (ZMod 2)) (X l.1)
    · simp
  exact Finset.mem_image.mpr ⟨l,hl,(Finset.mem_singleton.mp (hf hxl)).symm⟩

def Consistent {V : Type} (C : Clause V) : Prop :=
  ∀ i, ¬ ((i,true)∈C ∧ (i,false)∈C)

noncomputable def falsifying {V : Type} (C : Clause V) : V → Bool :=
  open Classical in fun i => if (i,true)∈C then false else true

theorem falsifying_spec {V : Type} (C : Clause V) (hC : Consistent C) : Falsifies (falsifying C) C := by
  rintro ⟨i,b⟩ hi
  cases b
  · have hnot : (i,true)∉C := fun hp => hC i ⟨hp,hi⟩
    simp [falsifying,hnot]
  · simp [falsifying,hi]

theorem vars_eq {V : Type} [DecidableEq V] (C : Clause V) (hC : Consistent C) :
    (polynomial C).vars=C.image Prod.fst := by
  apply Finset.Subset.antisymm (vars_subset C)
  intro x hx
  obtain ⟨⟨i,b⟩,hl,he⟩ := Finset.mem_image.mp hx
  dsimp only at he
  subst x
  by_contra hn
  let a := falsifying C
  let a' := Function.update a i b
  have hv : eval (toF2 a) (polynomial C)=1 := by rw [value,if_pos (falsifying_spec C hC)]
  have hnot : ¬ Falsifies a' C := by
    intro hf
    have hh := hf (i,b) hl
    exact hh (by simp [a'])
  have hv' : eval (toF2 a') (polynomial C)=0 := by rw [value,if_neg hnot]
  have heval : eval (toF2 a) (polynomial C)=eval (toF2 a') (polynomial C) := by
    apply eval₂Hom_congr' rfl _ rfl
    intro j hj hj'
    have hji : j≠i := by intro he; subst j; exact hn hj
    simp only [a',Function.update_of_ne hji,toF2]
  rw [hv,hv'] at heval
  exact one_ne_zero heval

theorem wclause_consistent {n w : ℕ} (C : WClause n w) : Consistent C.1 := by
  have hinj : Set.InjOn Prod.fst (↑C.1 : Set (Fin n×Bool)) :=
    (Finset.card_image_iff).mp (C.2.2.trans C.2.1.symm)
  intro i ⟨hp,hn⟩
  have he := hinj hp hn rfl
  have htf : true=false := congrArg Prod.snd he
  cases htf

end SemAC02.Supplement.P2MCNFExpansionPolynomials
end

section
-- Inlined Solutions.P2MWidthClauseEncoding

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MWidthClauseEncoding

open LiftSAParity

abbrev VarSet (n w : ℕ) := {S : Finset (Fin n) // S.card=w}
abbrev SignedSet (n w : ℕ) := (S : VarSet n w) × (S.1 → Bool)

noncomputable def encode {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : Clause (Fin n) :=
  Finset.univ.image (fun x : S => (x.1,b x))

theorem encode_card {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : (encode S b).card=S.card := by
  rw [encode,Finset.card_image_of_injective,Finset.card_univ,Fintype.card_coe]
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

theorem encode_vars {n : ℕ} (S : Finset (Fin n)) (b : S → Bool) : (encode S b).image Prod.fst=S := by
  ext i
  simp only [encode,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨l,⟨x,rfl⟩,rfl⟩
    exact x.2
  · intro hi
    exact ⟨(i,b ⟨i,hi⟩),⟨⟨i,hi⟩,rfl⟩,rfl⟩

noncomputable def pack {n w : ℕ} (z : SignedSet n w) : WClause n w :=
  ⟨encode z.1.1 z.2,(encode_card _ _).trans z.1.2,by rw [encode_vars]; exact z.1.2⟩

theorem encode_injective {n : ℕ} (S : Finset (Fin n)) (b c : S → Bool)
    (he : encode S b=encode S c) : b=c := by
  funext x
  have hx : (x.1,b x)∈encode S c := by
    rw [←he]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hx
  have hyx : y=x := Subtype.ext (congrArg Prod.fst hxy)
  subst y
  exact (congrArg Prod.snd hxy).symm

theorem pack_injective {n w : ℕ} : Function.Injective (pack : SignedSet n w → WClause n w) := by
  intro z z' he
  rcases z with ⟨S,b⟩
  rcases z' with ⟨T,c⟩
  have henc : encode S.1 b=encode T.1 c := congrArg Subtype.val he
  have hST : S=T := Subtype.ext (by
    have hv := congrArg (Finset.image Prod.fst) henc
    simpa only [encode_vars] using hv)
  subst T
  have hbc := encode_injective S.1 b c henc
  subst c
  rfl

noncomputable def labels {n w : ℕ} (C : WClause n w) (x : (C.1.image Prod.fst)) : Bool :=
  decide ((x.1,true)∈C.1)

theorem labels_eq {n w : ℕ} (C : WClause n w) (i : Fin n) (b : Bool) (hl : (i,b)∈C.1) :
    labels C ⟨i,Finset.mem_image.mpr ⟨(i,b),hl,rfl⟩⟩=b := by
  cases b
  · have hnot : (i,true)∉C.1 := fun h => P2MCNFExpansionPolynomials.wclause_consistent C i ⟨h,hl⟩
    simp [labels,hnot]
  · simp [labels,hl]

theorem pack_surjective {n w : ℕ} : Function.Surjective (pack : SignedSet n w → WClause n w) := by
  intro C
  refine ⟨⟨⟨C.1.image Prod.fst,C.2.2⟩,labels C⟩,?_⟩
  apply Subtype.ext
  ext l
  constructor
  · intro hl
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
    by_cases hb : labels C x=true
    · simpa only [hb] using (of_decide_eq_true hb : (x.1,true)∈C.1)
    · have hf : labels C x=false := Bool.eq_false_iff.mpr hb
      obtain ⟨⟨i,b⟩,hl,he⟩ := Finset.mem_image.mp x.2
      have he' : i=x.1 := he
      subst i
      have hlabel := labels_eq C x.1 b hl
      have hb' : b=labels C x := hlabel.symm
      simpa only [hb'] using hl
  · intro hl
    refine Finset.mem_image.mpr ⟨⟨l.1,Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩,Finset.mem_univ _,?_⟩
    exact Prod.ext rfl (labels_eq C l.1 l.2 hl)

noncomputable def equivalence (n w : ℕ) : SignedSet n w ≃ WClause n w :=
  Equiv.ofBijective pack ⟨pack_injective,pack_surjective⟩

theorem card (n w : ℕ) : Fintype.card (WClause n w)=n.choose w*2^w := by
  classical
  rw [←Fintype.card_congr (equivalence n w),Fintype.card_sigma]
  have hc (S : VarSet n w) : Fintype.card (S.1 → Bool)=2^w := by
    rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,S.2]
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  congr 1
  have he : Finset.univ.filter (fun S : Finset (Fin n) => S.card=w)=
      (Finset.univ : Finset (Fin n)).powersetCard w := by ext S; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

end SemAC02.Supplement.P2MWidthClauseEncoding
end

section
-- Inlined Solutions.P2MUniformFiniteProbability

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MUniformFiniteProbability

open SemAC02.Supplement

attribute [local instance] Classical.propDecidable

theorem nonneg {A : Type} [Fintype A] (E : A → Prop) : 0 ≤ uprob E := by unfold uprob; positivity

theorem le_one {A : Type} [Fintype A] (E : A → Prop) : uprob E ≤ 1 := by
  classical
  unfold uprob
  apply div_le_one_of_le₀
  · exact_mod_cast (Finset.card_le_univ (Finset.univ.filter E))
  · positivity

theorem mono {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a → F a) : uprob E ≤ uprob F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hs : Finset.univ.filter E⊆Finset.univ.filter F := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h a (Finset.mem_filter.mp ha).2⟩
  exact_mod_cast Finset.card_le_card hs

theorem complement {A : Type} [Fintype A] [Nonempty A] (E : A → Prop) :
    uprob (fun a => ¬ E a)=1-uprob E := by
  classical
  have hc : ((Finset.univ.filter (fun a => ¬ E a)).card : ℝ)+
      ((Finset.univ.filter E).card : ℝ)=Fintype.card A := by
    have hh := Finset.card_filter_add_card_filter_not (s:=Finset.univ) E
    have hn : (Finset.univ.filter (fun a => ¬ E a)).card+(Finset.univ.filter E).card=Fintype.card A := by
      simpa only [Finset.card_univ,Nat.add_comm] using hh
    exact_mod_cast hn
  have hn : (Fintype.card A : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uprob
  apply (eq_sub_iff_add_eq).mpr
  rw [Finset.filter_congr_decidable Finset.univ (fun a => ¬ E a) (Classical.decPred _)]
  rw [←add_div,hc,div_self hn]

theorem union_bound {A I : Type} [Fintype A] (S : Finset I) (E : A → Prop) (F : I → A → Prop)
    (h : ∀ a, E a → ∃ i∈S, F i a) : uprob E ≤ ∑ i∈S, uprob (F i) := by
  classical
  have hsub : Finset.univ.filter E⊆S.biUnion (fun i => Finset.univ.filter (F i)) := by
    intro a ha
    obtain ⟨i,hi,hFi⟩ := h a (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hFi⟩⟩
  have hc : ((Finset.univ.filter E).card : ℝ) ≤ ∑ i∈S, ((Finset.univ.filter (F i)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  unfold uprob
  rw [←Finset.sum_div]
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

noncomputable def productEventEquiv {A I : Type} (E : I → A → Prop) :
    {f : I → A // ∀ i, E i (f i)} ≃ ((i : I) → {a : A // E i a}) where
  toFun f i := ⟨f.1 i,f.2 i⟩
  invFun f := ⟨fun i => (f i).1,fun i => (f i).2⟩
  left_inv f := rfl
  right_inv f := rfl

theorem independent {A I : Type} [Fintype A] [Fintype I] [DecidableEq I] (E : I → A → Prop) :
    uprob (fun f : I → A => ∀ i, E i (f i))=∏ i, uprob (E i) := by
  classical
  have hc : ((Finset.univ.filter (fun f : I → A => ∀ i, E i (f i))).card : ℝ)=
      ∏ i, ((Finset.univ.filter (E i)).card : ℝ) := by
    rw [←Fintype.card_subtype,Fintype.card_congr (productEventEquiv E),Fintype.card_pi]
    simp only [Nat.cast_prod,Fintype.card_subtype]
  unfold uprob
  rw [Finset.filter_congr_decidable Finset.univ (fun f : I → A => ∀ i, E i (f i)) (Classical.decPred _)]
  rw [hc,Finset.prod_div_distrib]
  congr 1
  simp

theorem congr {A : Type} [Fintype A] (E F : A → Prop) (h : ∀ a, E a ↔ F a) : uprob E=uprob F :=
  le_antisymm (mono E F (fun a => (h a).mp)) (mono F E (fun a => (h a).mpr))

theorem true_event {A : Type} [Fintype A] [Nonempty A] : uprob (fun _ : A => True)=1 := by
  simp [uprob,Fintype.card_ne_zero]

theorem equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (E : B → Prop) :
    uprob (fun a => E (e a))=uprob E := by
  classical
  unfold uprob
  rw [Fintype.card_congr e]
  congr 1
  apply congrArg Nat.cast
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb he
    exact e.injective he
  · intro b hb
    exact ⟨e.symm b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using (Finset.mem_filter.mp hb).2⟩,e.apply_symm_apply b⟩

theorem coordinates {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    (J : Finset I) (E : A → Prop) :
    uprob (fun f : I → A => ∀ i∈J, E (f i))=(uprob E)^J.card := by
  classical
  rw [independent (fun i a => i∈J → E a)]
  have he (i : I) : uprob (fun a => i∈J → E a)=if i∈J then uprob E else 1 := by
    by_cases hi : i∈J
    · rw [if_pos hi]
      exact congr _ _ (fun a => by simp [hi])
    · rw [if_neg hi]
      exact (congr _ _ (fun a => by simp [hi])).trans true_event
  simp only [he]
  rw [←Finset.prod_filter]
  have hfilter : (Finset.univ : Finset I).filter (· ∈ J)=J := by ext i; simp
  rw [hfilter,Finset.prod_const]

theorem intersection_lower {A : Type} [Fintype A] [Nonempty A] (E F : A → Prop) :
    uprob E+uprob F-1 ≤ uprob (fun a => E a ∧ F a) := by
  classical
  have hb := union_bound (Finset.univ : Finset Bool) (fun a => ¬ (E a ∧ F a))
    (fun b a => if b then ¬ E a else ¬ F a) (by
      intro a ha
      by_cases he : E a
      · exact ⟨false,Finset.mem_univ _,by simpa using (fun hf => ha ⟨he,hf⟩)⟩
      · exact ⟨true,Finset.mem_univ _,by simpa using he⟩)
  have hh : uprob (fun a => ¬ (E a ∧ F a)) ≤ uprob (fun a => ¬ E a)+uprob (fun a => ¬ F a) := by
    simpa [Bool.forall_bool,add_comm] using hb
  rw [complement,complement,complement] at hh
  linarith

end ProofComplexity.P2MUniformFiniteProbability
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
-- Inlined Solutions.P2MWidthClauseCounts

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MWidthClauseCounts

open LiftSAParity P2MWidthClauseEncoding ProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

def variableSet {n w : ℕ} (C : WClause n w) : VarSet n w := ⟨C.1.image Prod.fst,C.2.2⟩

theorem variableSet_pack {n w : ℕ} (z : SignedSet n w) : variableSet (pack z)=z.1 :=
  Subtype.ext (encode_vars z.1.1 z.2)

theorem varSet_card (n w : ℕ) : Fintype.card (VarSet n w)=n.choose w := by
  classical
  have he : Finset.univ.filter (fun S : Finset (Fin n) => S.card=w)=
      (Finset.univ : Finset (Fin n)).powersetCard w := by ext S; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem fiber_count {n w : ℕ} (E : VarSet n w → Prop) :
    Fintype.card {C : WClause n w // E (variableSet C)}=
      Fintype.card {S : VarSet n w // E S}*2^w := by
  classical
  let e : {z : SignedSet n w // E z.1} ≃ {C : WClause n w // E (variableSet C)} :=
    (equivalence n w).subtypeEquiv (fun z => by change E z.1 ↔ E (variableSet (pack z)); rw [variableSet_pack])
  rw [←Fintype.card_congr e,Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun S : VarSet n w => S.1 → Bool) E),
    Fintype.card_sigma]
  have hc (S : {S : VarSet n w // E S}) : Fintype.card (S.1.1 → Bool)=2^w := by
    rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,S.1.2]
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]

theorem contained_sets {n w : ℕ} (A : Finset (Fin n)) :
    Fintype.card {S : VarSet n w // S.1⊆A}=A.card.choose w := by
  classical
  let e : {S : VarSet n w // S.1⊆A} ≃ {S : Finset (Fin n) // S∈A.powersetCard w} := {
    toFun S := ⟨S.1.1,Finset.mem_powersetCard.mpr ⟨S.2,S.1.2⟩⟩
    invFun S := ⟨⟨S.1,(Finset.mem_powersetCard.mp S.2).2⟩,(Finset.mem_powersetCard.mp S.2).1⟩
    left_inv S := rfl
    right_inv S := rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]

theorem contained_clauses {n w : ℕ} (A : Finset (Fin n)) :
    Fintype.card {C : WClause n w // C.1.image Prod.fst⊆A}=A.card.choose w*2^w := by
  change Fintype.card {C : WClause n w // (variableSet C).1⊆A}=_
  have hh := fiber_count (n:=n) (w:=w) (fun S => S.1⊆A)
  convert hh using 1
  · exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  · congr 1
    exact (contained_sets A).symm.trans (congrArg (@Fintype.card _) (Subsingleton.elim _ _))

theorem contained_probability {n w : ℕ} (hw : w ≤ n) (A : Finset (Fin n)) :
    uprob (fun C : WClause n w => C.1.image Prod.fst⊆A)=
      (A.card.choose w : ℝ)/(n.choose w : ℝ) := by
  classical
  unfold uprob
  rw [←Fintype.card_subtype,contained_clauses,P2MWidthClauseEncoding.card]
  push_cast
  exact mul_div_mul_right _ _ (by positivity : (2 : ℝ)^w≠0)

theorem contained_probability_bound {n w : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) (A : Finset (Fin n)) :
    uprob (fun C : WClause n w => C.1.image Prod.fst⊆A) ≤ ((A.card : ℝ)/(n : ℝ))^w := by
  rw [contained_probability hw A]
  exact AC02Frege.P2MSamplingJointProbabilities.choose_ratio_le n A.card w hn (by simpa using Finset.card_le_univ A) hw

theorem falsifies_encode {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) (b : S → Bool) :
    Falsifies y (encode S b) ↔ b=(fun x => !(y x.1)) := by
  constructor
  · intro hf
    funext x
    have hh := hf (x.1,b x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
    cases hy : y x.1 <;> cases hb : b x <;> simp_all
  · rintro rfl l hl
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
    simp

noncomputable def fixedSignsEquiv {n w : ℕ} (y : Fin n → Bool) :
    {z : SignedSet n w // z.2=(fun x => !(y x.1))} ≃ VarSet n w where
  toFun z := z.1.1
  invFun S := ⟨⟨S,fun x => !(y x.1)⟩,rfl⟩
  left_inv z := by
    rcases z with ⟨⟨S,b⟩,hb⟩
    apply Subtype.ext
    exact congrArg (Sigma.mk S) hb.symm
  right_inv S := rfl

theorem falsifying_clauses {n w : ℕ} (y : Fin n → Bool) :
    Fintype.card {C : WClause n w // Falsifies y C.1}=n.choose w := by
  classical
  let e : {z : SignedSet n w // z.2=(fun x => !(y x.1))} ≃ {C : WClause n w // Falsifies y C.1} :=
    (equivalence n w).subtypeEquiv (fun z => (falsifies_encode y z.1.1 z.2).symm)
  rw [←Fintype.card_congr e,Fintype.card_congr (fixedSignsEquiv y),varSet_card]

theorem falsification_probability {n w : ℕ} (hw : w ≤ n) (y : Fin n → Bool) :
    uprob (fun C : WClause n w => Falsifies y C.1)=(2 : ℝ)^(-(w : ℤ)) := by
  classical
  unfold uprob
  rw [Finset.filter_congr_decidable Finset.univ (fun C : WClause n w => Falsifies y C.1) (Classical.decPred _),
    ←Fintype.card_subtype,falsifying_clauses,P2MWidthClauseEncoding.card]
  have hc : (n.choose w : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hw).ne'
  push_cast
  rw [zpow_neg,zpow_natCast]
  field_simp

end SemAC02.Supplement.P2MWidthClauseCounts
end

section
-- Inlined Solutions.P2MRandomCNFUnsatisfiability

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomCNFUnsatisfiability

open LiftSAParity ProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

theorem sample_nonempty {n w : ℕ} (hw : w ≤ n) : Nonempty (WClause n w) := by
  apply Fintype.card_pos_iff.mp
  rw [P2MWidthClauseEncoding.card]
  exact Nat.mul_pos (Nat.choose_pos hw) (pow_pos (by decide) _)

theorem fixed_assignment {n w m : ℕ} (hw : w ≤ n) (y : Fin n → Bool) :
    uprob (fun ω : Fin m → WClause n w => ∀ j, ¬ Falsifies y (ω j).1)=
      (1-(2 : ℝ)^(-(w : ℤ)))^m := by
  letI := sample_nonempty hw
  rw [independent (fun _ : Fin m => fun C : WClause n w => ¬ Falsifies y C.1)]
  simp only [complement,P2MWidthClauseCounts.falsification_probability hw y,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

theorem satisfiable_probability {n w m : ℕ} (hw : w ≤ n) :
    uprob (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω)) ≤
      (2 : ℝ)^n*(1-(2 : ℝ)^(-(w : ℤ)))^m := by
  have hb := union_bound (Finset.univ : Finset (Fin n → Bool))
    (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω))
    (fun y ω => ∀ j, ¬ Falsifies y (ω j).1) (by
      rintro ω ⟨y,hy⟩
      refine ⟨y,Finset.mem_univ _,?_⟩
      intro j
      exact hy (ω j).1 (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  simpa only [fixed_assignment hw,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hb

theorem exponential_bound {n w m : ℕ} (hw : w ≤ n) :
    uprob (fun ω : Fin m → WClause n w => Satisfiable (seqCNF ω)) ≤
      Real.exp ((n : ℝ)*Real.log 2-(m : ℝ)*(2 : ℝ)^(-(w : ℤ))) := by
  apply (satisfiable_probability (m:=m) hw).trans
  have hp : 0 ≤ 1-(2 : ℝ)^(-(w : ℤ)) := by
    rw [zpow_neg,zpow_natCast]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have he : 1-(2 : ℝ)^(-(w : ℤ)) ≤ Real.exp (-(2 : ℝ)^(-(w : ℤ))) := by
    linarith [Real.add_one_le_exp (-(2 : ℝ)^(-(w : ℤ)))]
  calc
    (2 : ℝ)^n*(1-(2 : ℝ)^(-(w : ℤ)))^m ≤
        (2 : ℝ)^n*(Real.exp (-(2 : ℝ)^(-(w : ℤ))))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp he m) (by positivity)
    _ = _ := by
      have h2 : (2 : ℝ)^n=Real.exp ((n : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
      rw [h2,←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      ring

end SemAC02.Supplement.P2MRandomCNFUnsatisfiability
end

section
-- Inlined Solutions.P2MRandomCNFNeighborhood

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomCNFNeighborhood

open LiftSAParity ProofComplexity.P2MUniformFiniteProbability

attribute [local instance] Classical.propDecidable

noncomputable def neighborhood {n w m : ℕ} (ω : Fin m → WClause n w) (J : Finset (Fin m)) : Finset (Fin n) :=
  J.biUnion (fun j => (ω j).1.image Prod.fst)

theorem contained_iff {n w m : ℕ} (ω : Fin m → WClause n w) (J : Finset (Fin m)) (A : Finset (Fin n)) :
    neighborhood ω J⊆A ↔ ∀ j∈J, (ω j).1.image Prod.fst⊆A :=
  Finset.biUnion_subset

theorem containment_bound {n w m : ℕ} (hn : 1 ≤ n) (hw : w ≤ n)
    (J : Finset (Fin m)) (A : Finset (Fin n)) :
    uprob (fun ω : Fin m → WClause n w => neighborhood ω J⊆A) ≤
      ((A.card : ℝ)/(n : ℝ))^(w*J.card) := by
  letI := P2MRandomCNFUnsatisfiability.sample_nonempty hw
  rw [congr _ _ (fun ω => contained_iff ω J A),coordinates J (fun C : WClause n w => C.1.image Prod.fst⊆A)]
  rw [pow_mul]
  exact pow_le_pow_left₀ (nonneg _) (P2MWidthClauseCounts.contained_probability_bound hn hw A) _

theorem small_neighborhood_probability {n w m : ℕ} (hn : 1 ≤ n) (hw : w ≤ n)
    (t u : ℕ) (hu : u ≤ n) :
    uprob (fun ω : Fin m → WClause n w => ∃ J : Finset (Fin m), J.card=t ∧ (neighborhood ω J).card ≤ u) ≤
      (m.choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/(n : ℝ))^(w*t) := by
  let JS := (Finset.univ : Finset (Fin m)).powersetCard t
  let AS := (Finset.univ : Finset (Fin n)).powersetCard u
  have hcover : ∀ ω : Fin m → WClause n w,
      (∃ J : Finset (Fin m), J.card=t ∧ (neighborhood ω J).card ≤ u) →
      ∃ z∈JS×ˢAS, neighborhood ω z.1⊆z.2 := by
    rintro ω ⟨J,hJ,hN⟩
    obtain ⟨A,hNA,hAU,hA⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ (neighborhood ω J)) hN
      (by simpa using hu : u ≤ (Finset.univ : Finset (Fin n)).card)
    exact ⟨(J,A),Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hJ⟩,
      Finset.mem_powersetCard.mpr ⟨hAU,hA⟩⟩,hNA⟩
  apply (union_bound (JS×ˢAS) _ (fun z ω => neighborhood ω z.1⊆z.2) hcover).trans
  calc
    (∑ z∈JS×ˢAS, uprob (fun ω : Fin m → WClause n w => neighborhood ω z.1⊆z.2)) ≤
        ∑ _z∈JS×ˢAS, ((u : ℝ)/(n : ℝ))^(w*t) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hzJ,hzA⟩ := Finset.mem_product.mp hz
      have hJ := (Finset.mem_powersetCard.mp hzJ).2
      have hA := (Finset.mem_powersetCard.mp hzA).2
      simpa only [hJ,hA] using containment_bound hn hw z.1 z.2
    _ = _ := by simp [JS,AS,Finset.card_product,Finset.card_powersetCard,Nat.cast_mul]

end SemAC02.Supplement.P2MRandomCNFNeighborhood
end

section
-- Inlined Solutions.P2MBinomialExponentialUpperBound

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MBinomialExponentialUpperBound

theorem factorial_lower (k : ℕ) : ((k : ℝ)/Real.exp 1)^k ≤ (k.factorial : ℝ) := by
  by_cases hk : k=0
  · subst k; simp
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2*Real.pi*k) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ ((k : ℝ)/Real.exp 1)^k) hsqrt).trans
    (Stirling.le_factorial_stirling k)

theorem choose_upper (n k : ℕ) : (n.choose k : ℝ) ≤ (Real.exp 1*n/k)^k := by
  by_cases hk : k=0
  · subst k; simp
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0 < k by omega)
  have he : (0 : ℝ)<Real.exp 1 := Real.exp_pos _
  calc
    (n.choose k : ℝ) ≤ (n : ℝ)^k/(k.factorial : ℝ) := Nat.choose_le_pow_div k n
    _ ≤ (n : ℝ)^k/((k : ℝ)/Real.exp 1)^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (div_pos hkR he) k) (factorial_lower k)
    _ = _ := by rw [←div_pow]; congr 1; field_simp

end ProofComplexity.P2MBinomialExponentialUpperBound
end

section
-- Inlined Solutions.P2MNeighborhoodEntropyBound

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MNeighborhoodEntropyBound

theorem monotone_rounding (n a u v : ℝ) (hn : 0 < n) (hu : 0 < u)
    (huv : u ≤ v) (hvn : v ≤ n) (hua : u ≤ a) :
    u+(a-u)*Real.log (u/n) ≤ v+(a-v)*Real.log (v/n) := by
  have hv : 0 < v := hu.trans_le huv
  have hlog : Real.log (u/n) ≤ Real.log (v/n) :=
    Real.log_le_log (div_pos hu hn) (div_le_div_of_nonneg_right huv hn.le)
  have hln : Real.log (v/n) ≤ 0 := Real.log_nonpos (div_nonneg hv.le hn.le) ((div_le_one hn).mpr hvn)
  calc
    u+(a-u)*Real.log (u/n) ≤ u+(a-u)*Real.log (v/n) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hua)) u
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr huv) (neg_nonneg.mpr hln)]

theorem binomial_containment (n u b : ℕ) (hn : 0 < n) (hu : 0 < u) :
    (n.choose u : ℝ)*((u : ℝ)/n)^b ≤
      Real.exp ((u : ℝ)+((b : ℝ)-u)*Real.log ((u : ℝ)/n)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have huR : (0 : ℝ)<u := by exact_mod_cast hu
  apply (mul_le_mul_of_nonneg_right (P2MBinomialExponentialUpperBound.choose_upper n u) (by positivity)).trans
  have hpos : 0 < Real.exp 1*(n : ℝ)/u := by positivity
  have hA : (Real.exp 1*(n : ℝ)/u)^u=Real.exp ((u : ℝ)*(1-Real.log ((u : ℝ)/n))) := by
    rw [Real.exp_nat_mul,←Real.exp_log hpos]
    congr 1
    rw [Real.log_div (by positivity) huR.ne',Real.log_mul (Real.exp_pos _).ne' hnR.ne',Real.log_exp,
      Real.log_div huR.ne' hnR.ne']
    ring
  have hB : ((u : ℝ)/n)^b=Real.exp ((b : ℝ)*Real.log ((u : ℝ)/n)) := by
    rw [Real.exp_nat_mul,Real.exp_log (div_pos huR hnR)]
  rw [hA,hB,←Real.exp_add]
  apply le_of_eq
  congr 1
  ring

theorem binomial_pair (m n t u w : ℕ) (hm : 0 < m) (hn : 0 < n) (ht : 0 < t) (hu : 0 < u) :
    (m.choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/n)^(w*t) ≤
      Real.exp ((t : ℝ)*(1+Real.log ((m : ℝ)/t))+
        (u : ℝ)+((w : ℝ)*t-u)*Real.log ((u : ℝ)/n)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hb := binomial_containment n u (w*t) hn hu
  have he : (Real.exp 1*(m : ℝ)/t)^t=Real.exp ((t : ℝ)*(1+Real.log ((m : ℝ)/t))) := by
    rw [Real.exp_nat_mul,←Real.exp_log (by positivity : 0 < Real.exp 1*(m : ℝ)/t)]
    congr 1
    rw [Real.log_div (by positivity) htR.ne',Real.log_mul (Real.exp_pos _).ne' hmR.ne',Real.log_exp,
      Real.log_div hmR.ne' htR.ne']
    ring
  calc
    _ = (m.choose t : ℝ)*((n.choose u : ℝ)*((u : ℝ)/n)^(w*t)) := by ring
    _ ≤ (Real.exp 1*(m : ℝ)/t)^t*Real.exp ((u : ℝ)+(((w*t : ℕ) : ℝ)-u)*Real.log ((u : ℝ)/n)) :=
      mul_le_mul (P2MBinomialExponentialUpperBound.choose_upper m t) hb (by positivity) (by positivity)
    _ = _ := by rw [he,←Real.exp_add]; push_cast; congr 1; ring

end ProofComplexity.P2MNeighborhoodEntropyBound
end

section
-- Inlined Solutions.P2MRandomLogCNFEntropy

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomLogCNFEntropy

open ProofComplexity.P2MNeighborhoodEntropyBound

theorem exponent_bound (n m w t u : ℝ) (hn : 0 < n) (hw : 8 ≤ w) (ht : 0 < t)
    (hu : 0 < u) (hum : u ≤ 3*w*t/4)
    (hz : w*t/n ≤ Real.exp (-64))
    (hm : Real.log (m/t) ≤ Real.log w-Real.log (w*t/n)+w) :
    t*(1+Real.log (m/t))+u+(w*t-u)*Real.log (u/n) ≤ -(w*t) := by
  have hwpos : 0 < w := by linarith
  have ha : 0 < w*t := mul_pos hwpos ht
  have hzpos : 0 < w*t/n := div_pos ha hn
  have he1 : Real.exp (-64) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have han : w*t ≤ n := (div_le_one hn).mp (hz.trans he1)
  have hvpos : 0 < 3*w*t/4 := by positivity
  have hround := monotone_rounding n (w*t) u (3*w*t/4) hn hu hum (by nlinarith) (by nlinarith)
  have hlogv : Real.log ((3*w*t/4)/n) ≤ Real.log (w*t/n) :=
    Real.log_le_log (div_pos hvpos hn) (div_le_div_of_nonneg_right (by nlinarith) hn.le)
  have hlast : u+(w*t-u)*Real.log (u/n) ≤ w*t+(w*t/4)*Real.log (w*t/n) := by
    apply hround.trans
    have hh := mul_le_mul_of_nonneg_left hlogv (show 0 ≤ w*t-3*w*t/4 by nlinarith)
    nlinarith
  have hlz : Real.log (w*t/n) ≤ -64 :=
    (Real.log_le_log hzpos hz).trans_eq (Real.log_exp _)
  have hlw : Real.log w ≤ w-1 := Real.log_le_sub_one_of_pos hwpos
  have hcoef : w/8 ≤ w/4-1 := by linarith
  have hprod : (w/4-1)*Real.log (w*t/n) ≤ -8*w := by
    have hh := mul_le_mul_of_nonneg_left hlz (show 0 ≤ w/4-1 by linarith)
    nlinarith
  have hnormalized : 1+Real.log w+2*w+(w/4-1)*Real.log (w*t/n) ≤ -w := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hnormalized ht.le
  have hfirst := mul_le_mul_of_nonneg_left hm ht.le
  nlinarith

theorem clause_log (n w t : ℕ) (hn : 0 < n) (hw : 0 < w) (ht : 0 < t) :
    Real.log (((n*2^w : ℕ) : ℝ)/t) ≤
      Real.log (w : ℝ)-Real.log ((w : ℝ)*t/n)+w := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hwR : (0 : ℝ)<w := by exact_mod_cast hw
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hl2 : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)).trans_eq (by norm_num)
  push_cast
  rw [Real.log_div (by positivity) htR.ne',Real.log_mul hnR.ne' (by positivity),Real.log_pow,
    Real.log_div (by positivity) hnR.ne',Real.log_mul hwR.ne' htR.ne']
  nlinarith [mul_le_mul_of_nonneg_left hl2 hwR.le]

theorem union_term (n w t u : ℕ) (hn : 0 < n) (hw : 8 ≤ w) (ht : 0 < t) (hu : 0 < u)
    (hum : (u : ℝ) ≤ 3*w*t/4) (hz : (w : ℝ)*t/n ≤ Real.exp (-64)) :
    ((n*2^w).choose t : ℝ)*(n.choose u : ℝ)*((u : ℝ)/n)^(w*t) ≤
      Real.exp (-((w : ℝ)*t)) := by
  have hwpos : 0 < w := by omega
  have hm : 0 < n*2^w := Nat.mul_pos hn (pow_pos (by decide) w)
  apply (binomial_pair (n*2^w) n t u w hm hn ht hu).trans
  apply Real.exp_le_exp.mpr
  exact exponent_bound n ((n*2^w : ℕ) : ℝ) w t u (by exact_mod_cast hn) (by exact_mod_cast hw)
    (by exact_mod_cast ht) (by exact_mod_cast hu) hum hz (clause_log n w t hn hwpos ht)

end SemAC02.Supplement.P2MRandomLogCNFEntropy
end

section
-- Inlined Solutions.P2MRandomLogCNFNeighborhood

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomLogCNFNeighborhood

open ProofComplexity.P2MUniformFiniteProbability P2MRandomCNFNeighborhood

attribute [local instance] Classical.propDecidable

theorem single_size {n w : ℕ} (hn : 0 < n) (hw : 8 ≤ w) (hwn : w ≤ n)
    (t : ℕ) (ht : 0 < t) (hz : (w : ℝ)*t/n ≤ Real.exp (-64)) :
    uprob (fun ω : Fin (n*2^w) → WClause n w => ∃ J : Finset (Fin (n*2^w)),
      J.card=t ∧ ((neighborhood ω J).card : ℝ)<3*w*t/4) ≤ Real.exp (-((w : ℝ)*t)) := by
  let u : ℕ := ⌊3*(w : ℝ)*t/4⌋₊
  have hum : (u : ℝ) ≤ 3*(w : ℝ)*t/4 := Nat.floor_le (by positivity)
  have hwR : (0 : ℝ)<w := by exact_mod_cast (show 0 < w by omega)
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hsmall : (w : ℝ)*t ≤ n :=
    (div_le_one hnR).mp (hz.trans (Real.exp_le_one_iff.mpr (by norm_num)))
  have hun : u ≤ n := by
    have hh : (u : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  apply (mono _ (fun ω : Fin (n*2^w) → WClause n w => ∃ J : Finset (Fin (n*2^w)),
      J.card=t ∧ (neighborhood ω J).card ≤ u) (by
        rintro ω ⟨J,hJ,hbad⟩
        exact ⟨J,hJ,Nat.le_floor hbad.le⟩)).trans
  apply (small_neighborhood_probability (by omega) hwn t u hun).trans
  by_cases hu : u=0
  · rw [hu]
    have hwt : w*t≠0 := Nat.ne_of_gt (Nat.mul_pos (by omega : 0 < w) ht)
    simp only [Nat.cast_zero,zero_div,zero_pow hwt,mul_zero]
    exact (Real.exp_pos _).le
  · exact P2MRandomLogCNFEntropy.union_term n w t u hn hw ht (by omega) hum hz

theorem geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (s : ℕ) :
    (∑ j∈Finset.range s, q^(j+1)) ≤ q/(1-q) := by
  have hp : (∑ j∈Finset.range s, q^j) ≤ 1/(1-q) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
    have he := geom_sum_mul q s
    have hpow := pow_nonneg hq0 s
    nlinarith
  calc
    _ = q*(∑ j∈Finset.range s, q^j) := by rw [Finset.mul_sum]; simp only [pow_succ',mul_comm]
    _ ≤ q*(1/(1-q)) := mul_le_mul_of_nonneg_left hp hq0
    _ = _ := by ring

theorem failure_probability {n w : ℕ} (hn : 0 < n) (hw : 8 ≤ w) (hwn : w ≤ n)
    (s : ℕ) (hs : (w : ℝ)*s/n ≤ Real.exp (-64)) :
    uprob (fun ω : Fin (n*2^w) → WClause n w => ∃ J : Finset (Fin (n*2^w)),
      J.Nonempty ∧ J.card ≤ s ∧ ((neighborhood ω J).card : ℝ)<3*w*J.card/4) ≤
      Real.exp (-(w : ℝ))/(1-Real.exp (-(w : ℝ))) := by
  have hcover : ∀ ω : Fin (n*2^w) → WClause n w,
      (∃ J : Finset (Fin (n*2^w)), J.Nonempty ∧ J.card ≤ s ∧ ((neighborhood ω J).card : ℝ)<3*w*J.card/4) →
      ∃ j∈Finset.range s, ∃ J : Finset (Fin (n*2^w)), J.card=j+1 ∧ ((neighborhood ω J).card : ℝ)<3*w*((j+1 : ℕ) : ℝ)/4 := by
    rintro ω ⟨J,hJ,hJs,hbad⟩
    have hjpos := Finset.card_pos.mpr hJ
    refine ⟨J.card-1,Finset.mem_range.mpr (by omega),J,by omega,?_⟩
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ J.card)] using hbad
  apply (union_bound (Finset.range s) _
    (fun j ω => ∃ J : Finset (Fin (n*2^w)), J.card=j+1 ∧ ((neighborhood ω J).card : ℝ)<3*w*((j+1 : ℕ) : ℝ)/4) hcover).trans
  calc
    _ ≤ ∑ j∈Finset.range s, Real.exp (-(w : ℝ))^(j+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjs : j+1 ≤ s := by have hh := Finset.mem_range.mp hj; omega
      have hjsR : ((j+1 : ℕ) : ℝ) ≤ s := by exact_mod_cast hjs
      have hz : (w : ℝ)*((j+1 : ℕ) : ℝ)/n ≤ Real.exp (-64) := by
        apply le_trans _ hs
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left hjsR (Nat.cast_nonneg _)
      have hb := single_size hn hw hwn (j+1) (by omega) hz
      have he : Real.exp (-(w : ℝ))^(j+1)=Real.exp (-((w : ℝ)*((j+1 : ℕ) : ℝ))) := by
        rw [←Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      exact hb
    _ ≤ _ := by
      apply geometric_bound _ (Real.exp_pos _).le _ s
      apply Real.exp_lt_one_iff.mpr
      have hwR : (0 : ℝ)<w := by exact_mod_cast (show 0 < w by omega)
      linarith


end SemAC02.Supplement.P2MRandomLogCNFNeighborhood
end

section
-- Inlined Solutions.P2MClusterPolynomialEvaluation

namespace SemAC02.Supplement.P2MClusterPolynomialEvaluation

open MvPolynomial

theorem evaluation {σ L R : Type} [DecidableEq R] (P : ClusteredRep σ L R) (v : R)
    (α y : σ → ZMod 2) (p : MvPolynomial σ (ZMod 2)) :
    eval y (P.substCluster v α p)=eval (fun x => if P.cluster x=v then α x else y x) p := by
  classical
  let φ : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial σ (ZMod 2) :=
    aeval (fun x => if P.cluster x=v then C (α x) else X x)
  have hsub : P.substCluster v α p=φ p := by
    unfold ClusteredRep.substCluster
    apply congrArg (fun f : σ → MvPolynomial σ (ZMod 2) => aeval f p)
    funext x
    by_cases h : P.cluster x=v <;> simp [φ,h]
  rw [hsub]
  change ((eval y).comp φ.toRingHom) p=(eval (fun x => if P.cluster x=v then α x else y x)) p
  apply hom_congr_vars
  · ext a; simp [φ]
  · intro x hx hx'
    by_cases h : P.cluster x=v <;> simp [φ,h]
  · rfl

end SemAC02.Supplement.P2MClusterPolynomialEvaluation
end

section
-- Inlined Solutions.P2MExpansionCNFRepresentation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MExpansionCNFRepresentation

open MvPolynomial LiftSAParity AC02Frege AC02Frege.P2MBooleanAlgebra P2MCNFExpansionPolynomials

variable {V I : Type} [Finite V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def representation (C : I → Clause V) : ClusteredRep V I V where
  F0 := ∅
  Fu := fun u => {polynomial (C u)}
  cluster := id

theorem multilinear (C : I → Clause V) : ∀ p∈(representation C).axioms, IsMultilinear p := by
  rintro p (hp | ⟨u,hp⟩)
  · simp [representation] at hp
  · have he : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact P2MCNFExpansionPolynomials.multilinear _

theorem degrees (C : I → Clause V) (w : ℕ) (hw : ∀ u, (C u).card ≤ w) :
    ∀ p∈(representation C).axioms, p.totalDegree ≤ w := by
  rintro p (hp | ⟨u,hp⟩)
  · simp [representation] at hp
  · have he : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact (P2MCNFExpansionPolynomials.degree _).trans (hw u)

theorem graph_iff (C : I → Clause V) (hC : ∀ u, Consistent (C u)) (u : I) (v : V) :
    (representation C).graph.Adj u v ↔ v∈(C u).image Prod.fst := by
  constructor
  · rintro ⟨p,hp,x,hx,he⟩
    have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    have he' : x=v := he
    subst x
    rw [hp',P2MCNFExpansionPolynomials.vars_eq _ (hC u)] at hx
    exact hx
  · intro hv
    exact ⟨polynomial (C u),Set.mem_singleton _,v,by rwa [P2MCNFExpansionPolynomials.vars_eq _ (hC u)],rfl⟩

theorem respectful (C : I → Clause V) (hC : ∀ u, Consistent (C u)) :
    (representation C).IsRespectful := by
  intro J v u hboundary
  have hu : u∈J.filter (fun a => (representation C).graph.Adj a v) := by rw [hboundary]; simp
  have hv := (graph_iff C hC u v).mp (Finset.mem_filter.mp hu).2
  obtain ⟨⟨x,b⟩,hl,he⟩ := Finset.mem_image.mp hv
  dsimp only at he
  subst x
  refine ⟨fun _ => if b then 1 else 0,?_,?_⟩
  · intro p hp y
    have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
    rw [hp']
    let z : V → Bool := Function.update y v b
    have heval : eval (toF2 y) ((representation C).substCluster v (fun _ => if b then 1 else 0)
        (polynomial (C u)))=eval (toF2 z) (polynomial (C u)) := by
      rw [P2MClusterPolynomialEvaluation.evaluation]
      apply congrArg (fun f : V → ZMod 2 => eval f (polynomial (C u)))
      funext i
      by_cases hiv : i=v
      · subst i
        simp [representation,toF2,z]
      · simp [representation,hiv,toF2,z,Function.update_of_ne hiv]
    rw [heval,P2MCNFExpansionPolynomials.value]
    apply if_neg
    intro hf
    exact hf (v,b) hl (by simp [z])
  · intro g hg
    simp [representation] at hg

theorem encoded_axioms (C : I → Clause V) :
    polyAx (representation C).axioms=clauseAx (Set.range C) := by
  ext f
  constructor
  · rintro ⟨p,(hp | ⟨u,hp⟩),rfl⟩
    · simp [representation] at hp
    · have hp' : p=polynomial (C u) := Set.mem_singleton_iff.mp hp
      refine ⟨C u,⟨u,rfl⟩,?_⟩
      rw [hp']
      funext y
      exact eval_ml _ _
  · rintro ⟨D,⟨u,rfl⟩,rfl⟩
    refine ⟨polynomial (C u),Or.inr ⟨u,Set.mem_singleton _⟩,?_⟩
    funext y
    exact eval_ml _ _

end SemAC02.Supplement.P2MExpansionCNFRepresentation
end

section
-- Inlined Solutions.P2MFiniteFamilyBoundary

set_option maxHeartbeats 1000000

namespace ProofComplexity.P2MFiniteFamilyBoundary

variable {I V : Type} [DecidableEq V] [DecidableEq I]

noncomputable def neighbors (C : I → Finset V) (J : Finset I) := J.biUnion C
noncomputable def multiplicity (C : I → Finset V) (J : Finset I) (v : V) := (J.filter (fun j => v∈C j)).card
noncomputable def boundary (C : I → Finset V) (J : Finset I) :=
  (neighbors C J).filter (fun v => multiplicity C J v=1)

theorem double_count (C : I → Finset V) (J : Finset I) :
    ∑ v∈neighbors C J, multiplicity C J v=∑ j∈J, (C j).card := by
  classical
  simp only [multiplicity,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←Finset.sum_filter]
  have he : (neighbors C J).filter (fun v => v∈C j)=C j := by
    ext v
    constructor
    · intro hv; exact (Finset.mem_filter.mp hv).2
    · intro hv; exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j,hj,hv⟩,hv⟩
  rw [he]

theorem boundary_bound (C : I → Finset V) (J : Finset I) :
    2*(neighbors C J).card ≤ (boundary C J).card+∑ j∈J, (C j).card := by
  classical
  have hpoint (v : V) (hv : v∈neighbors C J) :
      2 ≤ (if multiplicity C J v=1 then 1 else 0)+multiplicity C J v := by
    have hn : 1 ≤ multiplicity C J v := by
      obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hv⟩⟩
    split_ifs <;> omega
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hh
  rw [double_count] at hh
  have hB : (∑ v∈neighbors C J, if multiplicity C J v=1 then 1 else 0)=(boundary C J).card := by
    simp only [boundary,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hB] at hh
  simpa only [Nat.mul_comm] using hh

end ProofComplexity.P2MFiniteFamilyBoundary
end

section
-- Inlined Solutions.P2MCNFBoundaryExpansion

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MCNFBoundaryExpansion

open LiftSAParity ProofComplexity.P2MFiniteFamilyBoundary P2MExpansionCNFRepresentation

variable {n w m : ℕ}

theorem boundary_eq (ω : Fin m → WClause n w) (J : Finset (Fin m)) :
    PCNonBool.boundaryOn (representation (fun j => (ω j).1)).graph Finset.univ J=
      boundary (fun j => (ω j).1.image Prod.fst) J := by
  classical
  let C := fun j => (ω j).1.image Prod.fst
  have hfilter (v : Fin n) :
      J.filter (fun j => (representation (fun i => (ω i).1)).graph.Adj j v)=J.filter (fun j => v∈C j) := by
    ext j
    simp only [Finset.mem_filter,graph_iff _ (fun i => P2MCNFExpansionPolynomials.wclause_consistent (ω i)),C]
  ext v
  simp only [PCNonBool.boundaryOn,Finset.mem_filter,Finset.mem_univ,true_and,hfilter,boundary,ProofComplexity.P2MFiniteFamilyBoundary.multiplicity]
  constructor
  · intro hv
    refine ⟨?_,hv⟩
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun j => v∈C j)).card)
    exact Finset.mem_biUnion.mpr ⟨j,(Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
  · exact And.right

theorem from_neighborhood (ω : Fin m → WClause n w) (s : ℕ)
    (hN : ∀ J : Finset (Fin m), J.Nonempty → J.card ≤ s →
      (3 : ℝ)*w*J.card/4 ≤ (P2MRandomCNFNeighborhood.neighborhood ω J).card) :
    IsBdryExp (representation (fun j => (ω j).1)).graph s ((w : ℝ)/2) := by
  intro J hJs
  have hJsn : J.card ≤ s := by exact_mod_cast hJs
  by_cases hne : J.Nonempty
  · have hb := boundary_bound (fun j => (ω j).1.image Prod.fst) J
    have hsum : (∑ j∈J, ((ω j).1.image Prod.fst).card)=w*J.card := by
      simp only [(fun j => (ω j).2.2),Finset.sum_const,smul_eq_mul,Nat.mul_comm]
    rw [hsum] at hb
    have hbR : 2*((P2MRandomCNFNeighborhood.neighborhood ω J).card : ℝ) ≤
        ((boundary (fun j => (ω j).1.image Prod.fst) J).card : ℝ)+(w : ℝ)*J.card := by exact_mod_cast hb
    rw [boundary_eq]
    have hn := hN J hne hJsn
    nlinarith
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst J
    simp [PCNonBool.boundaryOn]

end SemAC02.Supplement.P2MCNFBoundaryExpansion
end

section
-- Inlined Solutions.P2MRandomLogCNFUnsatisfiability

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MRandomLogCNFUnsatisfiability

open Filter Topology LiftSAParity ProofComplexity.P2MUniformFiniteProbability

theorem width_le (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow n.lt_two_pow_self.le

theorem probability_bound (n : ℕ) :
    uprob (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => Satisfiable (seqCNF ω)) ≤
      Real.exp ((n : ℝ)*(Real.log 2-1)) := by
  have hb := P2MRandomCNFUnsatisfiability.exponential_bound (m:=n*2^Nat.clog 2 n) (width_le n)
  have hm : ((n*2^Nat.clog 2 n : ℕ) : ℝ)*(2 : ℝ)^(-(Nat.clog 2 n : ℤ))=n := by
    rw [zpow_neg,zpow_natCast]
    push_cast
    field_simp
  rw [hm] at hb
  convert hb using 1 <;> congr 1 <;> ring

theorem satisfiable_tends_zero :
    Tendsto (fun n : ℕ => uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => Satisfiable (seqCNF ω))) atTop (𝓝 0) := by
  have hc : Real.log 2-1 < 0 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    linarith
  have he : Tendsto (fun n : ℕ => Real.exp ((n : ℝ)*(Real.log 2-1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.atTop_mul_const_of_neg hc tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun n => nonneg _) probability_bound he

theorem unsatisfiable_tends_one :
    Tendsto (fun n : ℕ => uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => ¬ Satisfiable (seqCNF ω))) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub satisfiable_tends_zero
  have he (n : ℕ) : uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => ¬ Satisfiable (seqCNF ω))=
      1-uprob (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => Satisfiable (seqCNF ω)) := by
    letI := P2MRandomCNFUnsatisfiability.sample_nonempty (width_le n)
    exact complement _
  simpa only [he,sub_zero] using ht

end SemAC02.Supplement.P2MRandomLogCNFUnsatisfiability
end

section
-- Inlined Solutions.P2MRandomLogCNFExpansion

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomLogCNFExpansion

open Filter Topology LiftSAParity ProofComplexity.P2MUniformFiniteProbability

noncomputable def supportSize (n : ℕ) : ℕ := ⌊Real.exp (-64)*n/(Nat.clog 2 n : ℝ)⌋₊

def Bad (n : ℕ) (ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n)) : Prop :=
  ∃ J : Finset (Fin (n*2^Nat.clog 2 n)), J.Nonempty ∧ J.card ≤ supportSize n ∧
    ((P2MRandomCNFNeighborhood.neighborhood ω J).card : ℝ)<3*(Nat.clog 2 n : ℝ)*J.card/4

theorem width_tendsto : Tendsto (fun n : ℕ => Nat.clog 2 n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2^b+1)] with n hn
  exact ((Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega : 2^b<n)).le

theorem support_budget (n : ℕ) (hn : 0 < n) (hw : 0 < Nat.clog 2 n) :
    (Nat.clog 2 n : ℝ)*supportSize n/n ≤ Real.exp (-64) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hwR : (0 : ℝ)<Nat.clog 2 n := by exact_mod_cast hw
  have hfloor : (supportSize n : ℝ) ≤ Real.exp (-64)*n/(Nat.clog 2 n : ℝ) := Nat.floor_le (by positivity)
  apply (div_le_iff₀ hnR).mpr
  have hh := mul_le_mul_of_nonneg_left hfloor hwR.le
  convert hh using 1 <;> field_simp <;> ring

theorem failure_tends_zero : Tendsto (fun n : ℕ => uprob (Bad n)) atTop (𝓝 0) := by
  have hwR : Tendsto (fun n : ℕ => (Nat.clog 2 n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp width_tendsto
  have hq : Tendsto (fun n : ℕ => Real.exp (-(Nat.clog 2 n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hwR
  have htail : Tendsto (fun n : ℕ => Real.exp (-(Nat.clog 2 n : ℝ))/(1-Real.exp (-(Nat.clog 2 n : ℝ)))) atTop (𝓝 0) := by
    have hd := hq.div ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hq) (by norm_num : (1 : ℝ)-0≠0)
    simp only [zero_div] at hd
    apply hd.congr
    intro n
    rfl
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => nonneg _)) _ htail
  filter_upwards [eventually_ge_atTop 1,width_tendsto.eventually_ge_atTop 8] with n hn hw
  exact P2MRandomLogCNFNeighborhood.failure_probability (by omega) hw (P2MRandomLogCNFUnsatisfiability.width_le n)
    (supportSize n) (support_budget n (by omega) (by omega))

theorem good_tends_one : Tendsto (fun n : ℕ => uprob (fun ω => ¬ Bad n ω)) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub failure_tends_zero
  have he (n : ℕ) : uprob (fun ω => ¬ Bad n ω)=1-uprob (Bad n) := by
    letI := P2MRandomCNFUnsatisfiability.sample_nonempty (P2MRandomLogCNFUnsatisfiability.width_le n)
    exact complement _
  simpa only [he,sub_zero] using ht

theorem boundary_expansion (n : ℕ) (ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n))
    (hω : ¬ Bad n ω) :
    IsBdryExp (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph
      (supportSize n) ((Nat.clog 2 n : ℝ)/2) := by
  apply P2MCNFBoundaryExpansion.from_neighborhood ω (supportSize n)
  intro J hJ hJs
  by_contra hn
  exact hω ⟨J,hJ,hJs,lt_of_not_ge hn⟩

end SemAC02.Supplement.P2MRandomLogCNFExpansion
end

section
-- Inlined Solutions.P2MRandomLogCNFExpansionTheorem

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomLogCNFExpansionTheorem

open Filter Topology LiftSAParity ProofComplexity.P2MUniformFiniteProbability P2MRandomLogCNFExpansion

attribute [local instance] Classical.propDecidable

theorem full :
    ∃ η : ℝ, 0 < η ∧ Tendsto (fun n : ℕ => uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
        ¬ Satisfiable (seqCNF ω) ∧ ∀ J : Finset (Fin (n*2^Nat.clog 2 n)),
          J.Nonempty → J.card ≤ ⌊η*n/(Nat.clog 2 n : ℝ)⌋₊ →
          (3 : ℝ)*(Nat.clog 2 n)*J.card/4 ≤
              ((J.biUnion (fun j => (ω j).1.image Prod.fst)).card : ℝ) ∧
          ((Nat.clog 2 n : ℝ)/2)*J.card ≤
              ((Finset.univ.filter (fun v : Fin n =>
                (J.filter (fun j => v∈(ω j).1.image Prod.fst)).card=1)).card : ℝ))) atTop (𝓝 1) := by
  refine ⟨Real.exp (-64),Real.exp_pos _,?_⟩
  have ht := ((P2MRandomLogCNFUnsatisfiability.unsatisfiable_tends_one.add good_tends_one).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  simp only [one_add_one_eq_two,show (2 : ℝ)-1=1 by norm_num] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds _ (fun n => le_one _)
  intro n
  letI := P2MRandomCNFUnsatisfiability.sample_nonempty (P2MRandomLogCNFUnsatisfiability.width_le n)
  apply (intersection_lower
    (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) => ¬ Satisfiable (seqCNF ω))
    (fun ω => ¬ Bad n ω)).trans
  apply mono
  rintro ω ⟨hunsat,hgood⟩
  refine ⟨hunsat,?_⟩
  intro J hJ hJs
  have hN : (3 : ℝ)*(Nat.clog 2 n)*J.card/4 ≤
      ((J.biUnion (fun j => (ω j).1.image Prod.fst)).card : ℝ) := by
    by_contra hn
    exact hgood ⟨J,hJ,hJs,lt_of_not_ge hn⟩
  refine ⟨hN,?_⟩
  have hJss : J.card ≤ supportSize n := by simpa only [supportSize] using hJs
  have hb := boundary_expansion n ω hgood J (by exact_mod_cast hJss)
  have he : PCNonBool.boundaryOn (P2MExpansionCNFRepresentation.representation (fun j => (ω j).1)).graph Finset.univ J=
      Finset.univ.filter (fun v : Fin n => (J.filter (fun j => v∈(ω j).1.image Prod.fst)).card=1) := by
    apply Finset.filter_congr
    intro v hv
    have hf : J.filter (fun j => (P2MExpansionCNFRepresentation.representation (fun i => (ω i).1)).graph.Adj j v)=
        J.filter (fun j => v∈(ω j).1.image Prod.fst) := by
      apply Finset.filter_congr
      intro j hj
      exact P2MExpansionCNFRepresentation.graph_iff _ (fun i => P2MCNFExpansionPolynomials.wclause_consistent (ω i)) j v
    rw [hf]
  rw [he] at hb
  exact hb

end SemAC02.Supplement.P2MRandomLogCNFExpansionTheorem
end

end P2MRandomLogExpansionProof
open SemAC02 SemAC02.Supplement MvPolynomial AC02Frege Filter Topology LiftSAParity

theorem solution :
    ∃ η : ℝ, 0 < η ∧ Tendsto (fun n : ℕ => uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
        ¬ Satisfiable (seqCNF ω) ∧ ∀ J : Finset (Fin (n*2^Nat.clog 2 n)),
          J.Nonempty → J.card ≤ ⌊η*n/(Nat.clog 2 n : ℝ)⌋₊ →
          (3 : ℝ)*(Nat.clog 2 n)*J.card/4 ≤
              ((J.biUnion (fun j => (ω j).1.image Prod.fst)).card : ℝ) ∧
          ((Nat.clog 2 n : ℝ)/2)*J.card ≤
              ((Finset.univ.filter (fun v : Fin n =>
                (J.filter (fun j => v∈(ω j).1.image Prod.fst)).card=1)).card : ℝ))) atTop (𝓝 1) := by
  exact P2MRandomLogExpansionProof.SemAC02.Supplement.P2MRandomLogCNFExpansionTheorem.full
