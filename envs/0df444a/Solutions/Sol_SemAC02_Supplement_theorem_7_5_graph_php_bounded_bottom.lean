-- Prove2me | solution 1 for SemAC02.Supplement.theorem_7_5_graph_php_bounded_bottom
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T10:53:06.609292+00:00
-- url     : https://prove2.me/submissions/2ad8b899-5350-4281-9404-356879b8717e

import Definitions.Def_SemAC02_Supplement_clauseAx
import Definitions.Def_SemAC02_Ble
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Supplement_randCNF
import Definitions.Def_SemAC02_Supplement_expansionRank
import Mathlib
import Definitions.Def_SemAC02_nDivision
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Supplement_phpG
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_IsPseudoRed
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Theorems.Thm_SemAC02_Supplement_lemma_5_3_expansion_pseudo_reduction
import Theorems.Thm_SemAC02_Supplement_theorem_5_4_rank_from_expansion
import Definitions.Def_PCNonBool_nbrOn
import Theorems.Thm_SemAC02_Supplement_theorem_4_5_spsp_rank_bound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_SemAC02_Supplement_ACirc

open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MGraphPHPBoundedBottomProof
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
-- Inlined Solutions.P2MDivisionBlockBasis

open Module

namespace SemAC02.P2MDivisionBlockBasis

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

end SemAC02.P2MDivisionBlockBasis
end

section
-- Inlined Solutions.P2MDivisionPoints

namespace SemAC02.P2MDivisionPoints

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

end SemAC02.P2MDivisionPoints
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
-- Inlined Solutions.P2MDivisionMonomialBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MDivisionMonomialBasis

noncomputable def divisionBasis (n h : ℕ) :
    Basis (Fin n → Option (Fin h)) (ZMod 2) (nDivOmega n h → ZMod 2) :=
  (P2MProofComplexity.productFunctionBasis (fun _i : Fin n => P2MDivisionBlockBasis.blockBasis h)).map
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (P2MDivisionPoints.pointEquiv n h).symm)

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
  change P2MProofComplexity.productFunctionBasis (fun _i : Fin n => P2MDivisionBlockBasis.blockBasis h) S
    ((P2MDivisionPoints.pointEquiv n h).symm X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply,P2MFibreBasis.xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [section_assemble]
  cases hs : S i with
  | none => simp only [P2MDivisionBlockBasis.blockBasis_none,xMon,Finset.prod_empty,map_one]
  | some j =>
    rw [P2MDivisionBlockBasis.blockBasis_some]
    change (if P2MDivisionPoints.decode n h X i = some j then 1 else 0) = _
    simp only [P2MDivisionPoints.decode_eq_some,xMon,Finset.prod_singleton,eval_X,toF2]

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

end SemAC02.P2MDivisionMonomialBasis
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
-- Inlined Solutions.P2MSingletonDivision

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MRelativeSpaceAlgebra

namespace SemAC02.P2MSingletonDivision

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
  rw [← P2MBooleanDimension.finrank_Ble n k, ← map_BleF0 n k]
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

end SemAC02.P2MSingletonDivision
end

section
-- Inlined Solutions.P2MDivisionSupports

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02.P2MDivisionMonomialBasis

namespace SemAC02.P2MDivisionSupports

def Valid {n h : ℕ} (A : Finset (Fin n × Fin h)) : Prop :=
  ∀ i j j', (i,j) ∈ A → (i,j') ∈ A → j = j'

noncomputable def pointOfSupport {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : nDivOmega n h := by
  classical
  refine ⟨fun v => decide (v ∈ A),?_⟩
  intro i j j' hj hj'
  exact hA i j j' (by simpa only [decide_eq_true_eq] using hj) (by simpa only [decide_eq_true_eq] using hj')

noncomputable def sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) : Fin n → Option (Fin h) :=
  P2MDivisionPoints.decode n h (pointOfSupport A hA)

theorem assemble_sections {n h : ℕ} (A : Finset (Fin n × Fin h)) (hA : Valid A) :
    assemble (sections A hA) = A := by
  classical
  ext v
  simp only [assemble,Finset.mem_filter,Finset.mem_univ,true_and,sections,P2MDivisionPoints.decode_eq_some,
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
  rw [P2MSingletonDivision.restrOmega_apply]
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
  simp only [P2MSingletonDivision.restrOmega_apply,Pi.smul_apply,smul_eq_mul]
  exact P2MMonomialLocality.eval_monomial_squarefree s c (toF2 X.1)

end SemAC02.P2MDivisionSupports
end

section
-- Inlined Solutions.P2MDivisionDegreeBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02.P2MDivisionMonomialBasis SemAC02.P2MDivisionSupports

namespace SemAC02.P2MDivisionDegreeBasis

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
        exact (P2MMonomialLocality.support_card_le_sum s).trans ((le_totalDegree hs).trans hpdeg)
      have he : restrOmega n h (xMon s.support) = divisionBasis n h S := by
        funext X
        rw [P2MSingletonDivision.restrOmega_apply,divisionBasis_apply]
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

end SemAC02.P2MDivisionDegreeBasis
end

section
-- Inlined Solutions.P2MDivisionFunctionAlgebra

open MvPolynomial

namespace SemAC02.P2MDivisionFunctionAlgebra

@[simp] theorem restriction_one (n h : ℕ) : restrOmega n h 1 = 1 := by
  funext X
  simp only [P2MSingletonDivision.restrOmega_apply,map_one,Pi.one_apply]

@[simp] theorem restriction_mul {n h : ℕ} (p q : MvPolynomial (Fin n × Fin h) (ZMod 2)) :
    restrOmega n h (p*q) = restrOmega n h p * restrOmega n h q := by
  funext X
  simp only [P2MSingletonDivision.restrOmega_apply,map_mul,Pi.mul_apply]

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

end SemAC02.P2MDivisionFunctionAlgebra
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
-- Inlined Solutions.P2MDivisionPolynomialRepresentative

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPolynomialRepresentative

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open P2MDivisionMonomialBasis P2MDivisionSupports

attribute [local instance] Classical.propDecidable

noncomputable def background (n h : ℕ) : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)) :=
  {p | ∃ i : Fin n, ∃ j j' : Fin h, j≠j' ∧ p=X (i,j)*X (i,j')}

noncomputable def representative (n h : ℕ) :
    (nDivOmega n h → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n×Fin h) (ZMod 2) :=
  (divisionBasis n h).constr (ZMod 2) (fun S => xMon (assemble S))

@[simp] theorem basis_value (n h : ℕ) (S : Fin n → Option (Fin h)) :
    representative n h (divisionBasis n h S)=xMon (assemble S) :=
  (divisionBasis n h).constr_basis (ZMod 2) _ S

theorem restriction_basis (n h : ℕ) (S : Fin n → Option (Fin h)) :
    restrOmega n h (xMon (assemble S))=divisionBasis n h S := by
  funext X
  exact (divisionBasis_apply n h S X).symm

theorem restriction_representative (n h : ℕ) (u : nDivOmega n h → ZMod 2) :
    restrOmega n h (representative n h u)=u := by
  have he : (restrOmega n h).comp (representative n h)=LinearMap.id := by
    apply (divisionBasis n h).ext
    intro S
    simp only [LinearMap.comp_apply,basis_value,LinearMap.id_apply,restriction_basis]
  exact LinearMap.congr_fun he u

theorem xMon_value {n h : ℕ} (A : Finset (Fin n×Fin h)) :
    representative n h (restrOmega n h (xMon A))=if Valid A then xMon A else 0 := by
  classical
  split_ifs with hv
  · have he : A=assemble (sections A hv) := (assemble_sections A hv).symm
    rw [he,restriction_basis,basis_value]
  · rw [xMon_invalid A hv,map_zero]

theorem monomial_value {n h : ℕ} (s : (Fin n×Fin h) →₀ ℕ) (a : ZMod 2) :
    representative n h (restrOmega n h (monomial s a))=
      if Valid s.support then a • xMon s.support else 0 := by
  classical
  rw [monomial_restriction,map_smul,xMon_value]
  split_ifs <;> simp

theorem degree_mem {n h k : ℕ} (u : nDivOmega n h → ZMod 2) (hu : u∈BleF0 n h k) :
    representative n h u∈Ble (Fin n×Fin h) k := by
  rw [P2MDivisionDegreeBasis.BleF0_eq_span] at hu
  change u∈Submodule.span (ZMod 2) _ at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S,rfl⟩ := hx
    rw [basis_value]
    exact Submodule.subset_span ⟨assemble S.1,(assemble_card S.1).le.trans S.2,rfl⟩
  | zero => simpa using (Ble (Fin n×Fin h) k).zero_mem
  | add u v hu hv ihu ihv => simpa only [map_add] using (Ble (Fin n×Fin h) k).add_mem ihu ihv
  | smul a u hu ihu => simpa only [map_smul] using (Ble (Fin n×Fin h) k).smul_mem a ihu

theorem invalid_mem_ideal {n h : ℕ} (A : Finset (Fin n×Fin h)) (hA : ¬ Valid A) :
    xMon A∈Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i}) := by
  classical
  unfold Valid at hA
  push_neg at hA
  obtain ⟨i,j,j',hj,hj',hne⟩ := hA
  have hpair : ({(i,j),(i,j')} : Finset (Fin n×Fin h))⊆A := by simp [Finset.insert_subset_iff,hj,hj']
  have he : xMon A=xMon (A\{(i,j),(i,j')})*(X (i,j)*X (i,j')) := by
    have hh := Finset.prod_sdiff hpair (f:=fun v : Fin n×Fin h => (X v : MvPolynomial (Fin n×Fin h) (ZMod 2)))
    simpa [xMon,hne] using hh.symm
  rw [he]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl ⟨i,j,j',hne,rfl⟩))

theorem sub_mem {n h : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2)) :
    p-representative n h (restrOmega n h p)∈
      Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i}) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [monomial_value]
    split_ifs with hv
    · have he : a • xMon s.support=ML (monomial s a) := by
        rw [ml_monomial,squarefree_monomial (sqfree s) a (by intro v; simp [sqfree,Finsupp.mapRange_apply]),sqfree_support]
      rw [he]
      exact P2MBooleanIdealMultilinearization.sub_mem _ _
    · rw [sub_zero]
      have hm : ML (monomial s a)∈Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i}) := by
        rw [ml_monomial]
        have hs : ∀ v, sqfree s v ≤ 1 := by intro v; simp [sqfree,Finsupp.mapRange_apply]
        rw [squarefree_monomial _ _ hs,sqfree_support]
        exact Submodule.smul_mem ((Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i})).restrictScalars (ZMod 2)) a (invalid_mem_ideal s.support hv)
      have hh := (Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i})).add_mem
        (P2MBooleanIdealMultilinearization.sub_mem (background n h) (monomial s a)) hm
      simpa only [sub_add_cancel] using hh
  | add p q hp hq =>
    rw [map_add,map_add]
    convert (Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i})).add_mem hp hq using 1 <;> ring

end SemAC02.Supplement.P2MDivisionPolynomialRepresentative
end

section
-- Inlined Solutions.P2MDivisionBackgroundStandard

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionBackgroundStandard

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open P2MDivisionSupports P2MDivisionPolynomialRepresentative

 theorem valid_coefficient {n h : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : IsMultilinear p) (d : (Fin n×Fin h) →₀ ℕ) (hd : Valid d.support) :
    coeff d (representative n h (restrOmega n h p))=coeff d p := by
  classical
  conv_lhs => rw [p.as_sum,map_sum,map_sum,coeff_sum]
  conv_rhs => rw [p.as_sum,coeff_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [monomial_value]
  split_ifs with hv
  · rw [←squarefree_monomial e (coeff e p) (hp e he)]
  · have hne : e≠d := by intro hed; exact hv (hed.symm ▸ hd)
    simp [coeff_monomial,hne]

 theorem ideal_restriction_zero {n h : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p∈Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=X i^2-X i})) :
    restrOmega n h p=0 := by
  funext X
  have hker : Ideal.span (background n h ∪ {p | ∃ i : Fin n×Fin h, p=MvPolynomial.X i^2-MvPolynomial.X i}) ≤
      RingHom.ker (eval (toF2 X.1)) := by
    apply Ideal.span_le.mpr
    rintro q (⟨i,j,j',hne,rfl⟩ | ⟨v,rfl⟩)
    · change eval (toF2 X.1) (MvPolynomial.X (i,j)*MvPolynomial.X (i,j'))=0
      simp only [map_mul,eval_X]
      cases hx : X.1 (i,j) <;> cases hy : X.1 (i,j') <;> simp [toF2,hx,hy]
      exact (hne (X.2 i j j' hx hy)).elim
    · change eval (toF2 X.1) (MvPolynomial.X v^2-MvPolynomial.X v)=0
      cases hx : X.1 v <;> simp [toF2,hx]
  exact hker hp

 theorem irreducible {n h : ℕ} (m : MonomialOrder (Fin n×Fin h))
    (A : Finset (Fin n×Fin h)) (hA : Valid A) : IsIrred m (background n h) A := by
  intro p hp hn he
  have hvalid : Valid (m.degree p).support := by
    rw [he,xMon_eq_monomial,m.degree_monomial,if_neg one_ne_zero,indicator_support]
    exact hA
  have hc := valid_coefficient p hp.1 (m.degree p) hvalid
  rw [ideal_restriction_zero p hp.2,map_zero,coeff_zero] at hc
  exact (mem_support_iff.mp (m.degree_mem_support hn)) hc.symm

 theorem pair_multilinear {n h : ℕ} (i : Fin n) (j j' : Fin h) (hne : j≠j') :
    IsMultilinear (X (i,j)*X (i,j') : MvPolynomial (Fin n×Fin h) (ZMod 2)) := by
  have he : (X (i,j)*X (i,j') : MvPolynomial (Fin n×Fin h) (ZMod 2))=xMon {(i,j),(i,j')} := by
    simp [xMon,hne]
  rw [he]
  exact xMon_multilinear _

 theorem background_multilinear {n h : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p∈background n h) : IsMultilinear p := by
  obtain ⟨i,j,j',hne,rfl⟩ := hp
  exact pair_multilinear i j j' hne

 theorem background_degree {n h : ℕ} (p : MvPolynomial (Fin n×Fin h) (ZMod 2))
    (hp : p∈background n h) : p.totalDegree ≤ 2 := by
  obtain ⟨i,j,j',hne,rfl⟩ := hp
  exact (totalDegree_mul _ _).trans (by simp)

end SemAC02.Supplement.P2MDivisionBackgroundStandard
end

section
-- Inlined Solutions.P2MPaddedPHPRepresentation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPaddedPHPRepresentation

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra LiftSAParity
open P2MDivisionPolynomialRepresentative

variable {L : Type} [Fintype L] [DecidableEq L] {n D : ℕ}

noncomputable def rowVariables (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) : Finset (Fin n×Fin D) :=
  (PCNonBool.nbrOn G Finset.univ u).attach.image
    (fun v => (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩))

noncomputable def rowClause (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) : Clause (Fin n×Fin D) :=
  (rowVariables G ι u).image (fun x => (x,true))

noncomputable def representation (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) : ClusteredRep (Fin n×Fin D) L (Fin n) where
  F0 := background n D
  Fu := fun u => {P2MCNFExpansionPolynomials.polynomial (rowClause G ι u)}
  cluster := Prod.fst

 theorem consistent (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) :
    P2MCNFExpansionPolynomials.Consistent (rowClause G ι u) := by
  classical
  intro x hx
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hx.2
  have hh := congrArg Prod.snd he
  cases hh

 theorem row_vars (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) :
    (P2MCNFExpansionPolynomials.polynomial (rowClause G ι u)).vars=rowVariables G ι u := by
  rw [P2MCNFExpansionPolynomials.vars_eq _ (consistent G ι u),rowClause,Finset.image_image]
  simp [Function.comp_def]

 theorem row_degree (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) :
    (P2MCNFExpansionPolynomials.polynomial (rowClause G ι u)).totalDegree ≤ (PCNonBool.nbrOn G Finset.univ u).card := by
  apply (P2MCNFExpansionPolynomials.degree _).trans
  exact Finset.card_image_le.trans (Finset.card_image_le.trans (by simp))

 theorem graph_iff (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) (v : Fin n) :
    (representation G ι).graph.Adj u v ↔ G.Adj u v := by
  classical
  constructor
  · rintro ⟨p,hp,x,hx,he⟩
    have hp' : p=P2MCNFExpansionPolynomials.polynomial (rowClause G ι u) := Set.mem_singleton_iff.mp hp
    rw [hp',row_vars] at hx
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
    have hav : a.1=v := (congrArg Prod.fst hax).trans he
    rw [←hav]
    simpa [PCNonBool.nbrOn] using a.2
  · intro huv
    let hv : v∈PCNonBool.nbrOn G Finset.univ u := by simpa [PCNonBool.nbrOn] using huv
    refine ⟨P2MCNFExpansionPolynomials.polynomial (rowClause G ι u),Set.mem_singleton _,(v,ι v ⟨u,huv⟩),?_,rfl⟩
    rw [row_vars]
    exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_attach _ _,rfl⟩

 theorem graph_eq (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) : (representation G ι).graph=G := by
  have extG (G H : PCNonBool.BipGraph L (Fin n)) (he : G.Adj=H.Adj) : G=H := by
    cases G with
    | mk a =>
      cases H with
      | mk b =>
        dsimp only at he
        cases he
        congr
  apply extG
  funext u v
  exact propext (graph_iff G ι u v)

 theorem multilinear (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) :
    ∀ p∈(representation G ι).axioms, IsMultilinear p := by
  rintro p (hp | ⟨u,hp⟩)
  · exact P2MDivisionBackgroundStandard.background_multilinear p hp
  · have he : p=P2MCNFExpansionPolynomials.polynomial (rowClause G ι u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact P2MCNFExpansionPolynomials.multilinear _

 theorem degrees (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D)
    (δ : ℕ) (hδ : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ δ) :
    ∀ p∈(representation G ι).axioms, p.totalDegree ≤ max 2 δ := by
  rintro p (hp | ⟨u,hp⟩)
  · exact (P2MDivisionBackgroundStandard.background_degree p hp).trans (le_max_left _ _)
  · have he : p=P2MCNFExpansionPolynomials.polynomial (rowClause G ι u) := Set.mem_singleton_iff.mp hp
    rw [he]
    exact ((row_degree G ι u).trans (hδ u)).trans (le_max_right _ _)

 theorem raw_row (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (u : L) :
    clausePolyF (F:=ZMod 2) (rowClause G ι u)=
      ∏ v∈(PCNonBool.nbrOn G Finset.univ u).attach,
        (1-X (v.1,ι v.1 ⟨u,by simpa [PCNonBool.nbrOn] using v.2⟩)) := by
  classical
  unfold clausePolyF rowClause
  rw [Finset.prod_image (by intro a ha b hb he; exact congrArg Prod.fst he)]
  simp only [litPolyF,ite_true]
  unfold rowVariables
  rw [Finset.prod_image]
  intro a ha b hb he
  exact Subtype.ext (congrArg Prod.fst he)

 theorem encoded_axioms (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) :
    polyAx (representation G ι).axioms=polyAx (phpPadded G ι) := by
  ext f
  constructor
  · rintro ⟨p,(hp | ⟨u,hp⟩),rfl⟩
    · exact ⟨p,Or.inl hp,rfl⟩
    · have he : p=P2MCNFExpansionPolynomials.polynomial (rowClause G ι u) := Set.mem_singleton_iff.mp hp
      refine ⟨clausePolyF (rowClause G ι u),Or.inr ⟨u,raw_row G ι u⟩,?_⟩
      rw [he]
      funext y
      exact (eval_ml _ _).symm
  · rintro ⟨p,(hp | ⟨u,rfl⟩),rfl⟩
    · exact ⟨p,Or.inl hp,rfl⟩
    · refine ⟨P2MCNFExpansionPolynomials.polynomial (rowClause G ι u),Or.inr ⟨u,Set.mem_singleton _⟩,?_⟩
      funext y
      change eval (toF2 y) (ML (clausePolyF (rowClause G ι u)))=_
      rw [eval_ml,raw_row]
      rfl

end SemAC02.Supplement.P2MPaddedPHPRepresentation
end

section
-- Inlined Solutions.P2MPaddedPHPRespectfulness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPaddedPHPRespectfulness

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra
open P2MPaddedPHPRepresentation

 theorem respectful {L : Type} [Fintype L] [DecidableEq L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) : (representation G ι).IsRespectful := by
  classical
  intro J v u hboundary
  have hu : u∈J.filter (fun a => (representation G ι).graph.Adj a v) := by rw [hboundary]; simp
  have huv : G.Adj u v := (graph_iff G ι u v).mp (Finset.mem_filter.mp hu).2
  let j0 := ι v ⟨u,huv⟩
  let α : Fin n×Fin D → ZMod 2 := fun x => if x.2=j0 then 1 else 0
  refine ⟨α,?_,?_⟩
  · intro p hp y
    have hp' : p=P2MCNFExpansionPolynomials.polynomial (rowClause G ι u) := Set.mem_singleton_iff.mp hp
    rw [hp',P2MClusterPolynomialEvaluation.evaluation,P2MCNFExpansionPolynomials.polynomial,eval_ml,raw_row,map_prod]
    have hv : v∈PCNonBool.nbrOn G Finset.univ u := by simpa [PCNonBool.nbrOn] using huv
    apply Finset.prod_eq_zero (Finset.mem_attach _ ⟨v,hv⟩)
    simp [representation,α,j0]
  · rintro g ⟨i,j,j',hne,rfl⟩
    by_cases hi : i=v
    · left
      intro y
      rw [P2MClusterPolynomialEvaluation.evaluation,map_mul,eval_X,eval_X]
      by_cases hj : j=j0 <;> by_cases hj' : j'=j0
      · exact (hne (hj.trans hj'.symm)).elim
      all_goals simp [representation,hi,α,hj,hj']
    · right
      intro y
      rw [P2MClusterPolynomialEvaluation.evaluation,map_mul,eval_X,eval_X,map_mul,eval_X,eval_X]
      simp [representation,hi]

end SemAC02.Supplement.P2MPaddedPHPRespectfulness
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
-- Inlined Solutions.P2MDivisionPseudoReductionNormalization

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPseudoReductionNormalization

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces
open P2MDivisionPolynomialRepresentative P2MDivisionSupports

variable {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

lemma restriction_mem (p : MvPolynomial (Fin n×Fin h) (ZMod 2)) (hp : p∈Ble (Fin n×Fin h) B) :
    restrOmega n h p∈BleF0 n h B :=
  ⟨p,(mem_restrictTotalDegree _ _ _).mpr ((mem_Ble_iff B p).mp hp).2,rfl⟩

noncomputable def normalizeMap (n h B : ℕ) : Ble (Fin n×Fin h) B →ₗ[ZMod 2] Ble (Fin n×Fin h) B where
  toFun p := ⟨representative n h (restrOmega n h p),degree_mem _ (restriction_mem _ p.2)⟩
  map_add' p q := Subtype.ext (by simp only [Submodule.coe_add,map_add])
  map_smul' a p := Subtype.ext (by simp only [Submodule.coe_smul,map_smul,RingHom.id_apply])

 theorem monomial_upward (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)))
    (R : Ble (Fin n×Fin h) B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (S T : Finset (Fin n×Fin h)) (hB : (S∪T).card ≤ B) (hS : S.card ≤ B)
    (hz : R ⟨xMon S,Submodule.subset_span ⟨S,hS,rfl⟩⟩=0) :
    R ⟨xMon (S∪T),Submodule.subset_span ⟨S∪T,hB,rfl⟩⟩=0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.union_empty] using hz
  | @insert x T hx ih =>
    have hOld : (S∪T).card ≤ B := (Finset.card_le_card (Finset.union_subset_union_right (Finset.subset_insert x T))).trans hB
    have hProd : ML (X x*xMon (S∪T))∈Ble (Fin n×Fin h) B := by
      rw [P2MBooleanVariableProducts.monomial_insert,←Finset.union_insert]
      exact Submodule.subset_span ⟨S∪insert x T,hB,rfl⟩
    have hh := hR.2 ⟨xMon (S∪T),Submodule.subset_span ⟨S∪T,hOld,rfl⟩⟩ x hProd (ih hOld)
    simpa only [P2MBooleanVariableProducts.monomial_insert,←Finset.union_insert] using hh

 theorem invalid_zero (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)))
    (hF : background n h⊆F) (R : Ble (Fin n×Fin h) B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (A : Finset (Fin n×Fin h)) (hA : ¬ Valid A) (hAB : A.card ≤ B) :
    R ⟨xMon A,Submodule.subset_span ⟨A,hAB,rfl⟩⟩=0 := by
  classical
  unfold Valid at hA
  push_neg at hA
  obtain ⟨i,j,j',hj,hj',hne⟩ := hA
  let S : Finset (Fin n×Fin h) := {(i,j),(i,j')}
  have hSub : S⊆A := by simp [S,Finset.insert_subset_iff,hj,hj']
  have hSB : S.card ≤ B := (Finset.card_le_card hSub).trans hAB
  have hmem : xMon S∈F := hF ⟨i,j,j',hne,by simp [S,xMon,hne]⟩
  have hz := hR.1 (xMon S) hmem (Submodule.subset_span ⟨S,hSB,rfl⟩)
  have hh := monomial_upward F R hR S A (by simpa only [Finset.union_eq_right.mpr hSub] using hAB) hSB hz
  simpa only [Finset.union_eq_right.mpr hSub] using hh

 theorem normalize_eq (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2)))
    (hF : background n h⊆F) (R : Ble (Fin n×Fin h) B →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (p : Ble (Fin n×Fin h) B) : R (normalizeMap n h B p)=R p := by
  classical
  have hh : ∀ q (hq : q∈Ble (Fin n×Fin h) B),
      R (normalizeMap n h B ⟨q,hq⟩)=R ⟨q,hq⟩ := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A,hAB,rfl⟩ := hx
      by_cases hv : Valid A
      · have he : normalizeMap n h B ⟨xMon A,Submodule.subset_span ⟨A,hAB,rfl⟩⟩=
            ⟨xMon A,Submodule.subset_span ⟨A,hAB,rfl⟩⟩ := by
          apply Subtype.ext
          exact (xMon_value A).trans (if_pos hv)
        rw [he]
      · have he : normalizeMap n h B ⟨xMon A,Submodule.subset_span ⟨A,hAB,rfl⟩⟩=0 := by
          apply Subtype.ext
          exact (xMon_value A).trans (if_neg hv)
        rw [he,map_zero,invalid_zero F hF R hR A hv hAB]
    | zero => exact (map_zero (R.comp (normalizeMap n h B))).trans (map_zero R).symm
    | add u v hu hv ihu ihv =>
      change (R.comp (normalizeMap n h B)) (⟨u,hu⟩+⟨v,hv⟩)=R (⟨u,hu⟩+⟨v,hv⟩)
      simp only [map_add,LinearMap.comp_apply,ihu,ihv]
    | smul a u hu ihu =>
      change (R.comp (normalizeMap n h B)) (a • ⟨u,hu⟩)=R (a • ⟨u,hu⟩)
      simp only [map_smul,LinearMap.comp_apply,ihu]
  exact hh p p.2

end SemAC02.Supplement.P2MDivisionPseudoReductionNormalization
end

section
-- Inlined Solutions.P2MDivisionPseudoReductionDescent

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MDivisionPseudoReductionDescent

open MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra P2MBooleanDegreeSpaces
open P2MDivisionPolynomialRepresentative P2MDivisionPseudoReductionNormalization

noncomputable def representativeMap (n h B K : ℕ) (hBK : B ≤ K) :
    BleF0 n h B →ₗ[ZMod 2] Ble (Fin n×Fin h) K where
  toFun p := ⟨representative n h p,P2MPseudoReductionRestriction.ble_mono hBK (degree_mem _ p.2)⟩
  map_add' p q := Subtype.ext (by simp only [Submodule.coe_add,map_add])
  map_smul' a p := Subtype.ext (by simp only [Submodule.coe_smul,map_smul,RingHom.id_apply])

noncomputable def reduction {n h B K : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble (Fin n×Fin h) K →ₗ[ZMod 2] W) (hBK : B ≤ K) : BleF0 n h B →ₗ[ZMod 2] W :=
  R.comp (representativeMap n h B K hBK)

 theorem pseudo {n h B : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (hF0 : background n h⊆F)
    (hF : ∀ f∈F, f∈Ble (Fin n×Fin h) B)
    (R : Ble (Fin n×Fin h) (B+1) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R) :
    IsPseudoRedF0 F (reduction R (Nat.le_succ B)) := by
  constructor
  · intro f hf hfB
    have hfK : f∈Ble (Fin n×Fin h) (B+1) := P2MPseudoReductionRestriction.ble_mono (Nat.le_succ B) (hF f hf)
    have hh := normalize_eq F hF0 R hR ⟨f,hfK⟩
    exact hh.trans (hR.1 f hf hfK)
  · intro p v hv hz
    let u := representative n h (p : nDivOmega n h → ZMod 2)
    have huB : u∈Ble (Fin n×Fin h) B := degree_mem _ p.2
    have huK := P2MPseudoReductionRestriction.ble_mono (Nat.le_succ B) huB
    let q := ML (X v*u)
    have hq : q∈Ble (Fin n×Fin h) (B+1) := by
      apply (mem_Ble_iff (B+1) q).mpr
      refine ⟨ml_multilinear _,?_⟩
      apply (P2MBooleanFlip.ml_totalDegree_le _).trans
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_X]
      have hh := ((mem_Ble_iff B u).mp huB).2
      omega
    have hEval : restrOmega n h q=(fun x : nDivOmega n h => toF2 x.1 v*(p : nDivOmega n h → ZMod 2) x) := by
      have he := restriction_representative n h (p : nDivOmega n h → ZMod 2)
      funext x
      rw [P2MSingletonDivision.restrOmega_apply]
      dsimp [q]
      rw [eval_ml,map_mul,eval_X]
      congr 1
      exact congrFun he x
    have hzero : R ⟨u,huK⟩=0 := hz
    have hprod := hR.2 ⟨u,huK⟩ v hq hzero
    have hnorm := normalize_eq F hF0 R hR ⟨q,hq⟩
    change R (representativeMap n h B (B+1) (Nat.le_succ B) ⟨_,hv⟩)=0
    have he : representativeMap n h B (B+1) (Nat.le_succ B) ⟨_,hv⟩=
        normalizeMap n h (B+1) ⟨q,hq⟩ := by
      apply Subtype.ext
      exact congrArg (representative n h) hEval.symm
    rw [he]
    exact hnorm.trans hprod

 theorem rank_eq {n h B K : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Set (MvPolynomial (Fin n×Fin h) (ZMod 2))) (hF0 : background n h⊆F)
    (R : Ble (Fin n×Fin h) K →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (hBK : B ≤ K) (k : ℕ) (hk : k ≤ B) :
    rankLeF0 (reduction R hBK) k=rankLe R k := by
  have heq : (Submodule.comap (BleF0 n h B).subtype (BleF0 n h k)).map (reduction R hBK)=
      (Submodule.comap (Ble (Fin n×Fin h) K).subtype (Ble (Fin n×Fin h) k)).map R := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨representativeMap n h B K hBK p,degree_mem _ hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      have hu : restrOmega n h (p : MvPolynomial (Fin n×Fin h) (ZMod 2))∈BleF0 n h k := restriction_mem _ hp
      have huB := P2MDivisionFunctionAlgebra.degree_mono hk hu
      refine ⟨⟨restrOmega n h (p : MvPolynomial (Fin n×Fin h) (ZMod 2)),huB⟩,hu,?_⟩
      exact normalize_eq F hF0 R hR p
  unfold rankLeF0 rankLe
  rw [heq]

end SemAC02.Supplement.P2MDivisionPseudoReductionDescent
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
-- Inlined Solutions.P2MDegreeLexCompatibility

namespace SemAC02.Supplement.P2MDegreeLexCompatibility

theorem compatible {σ : Type} [LinearOrder σ] [WellFoundedGT σ] :
    IsDegCompatible (MonomialOrder.degLex : MonomialOrder σ) := by
  intro a b hab
  change toDegLex a < toDegLex b
  rw [Finsupp.DegLex.lt_iff]
  exact Or.inl hab

end SemAC02.Supplement.P2MDegreeLexCompatibility
end

section
-- Inlined Solutions.P2MPaddedPHPOperatorWitness

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MPaddedPHPOperatorWitness

open MvPolynomial AC02Frege P2MPaddedPHPRepresentation P2MBooleanDegreeSpaces

local instance variableOrder (n D : ℕ) : LinearOrder (Fin n×Fin D) :=
  LinearOrder.lift' (toLex : (Fin n×Fin D) → Lex (Fin n×Fin D)) (fun _ _ he => he)

local instance variableWellFounded (n D : ℕ) : @WellFoundedGT (Fin n×Fin D) (variableOrder n D).toLT :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

 theorem exists_reduction {L : Type} [Fintype L] [DecidableEq L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (hD : 0 < D)
    (δ : ℕ) (hδ : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ δ)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c) (hexp : IsBdryExp G s c)
    (B : ℕ) (hdB : max 2 δ ≤ B) (hBudget : (B : ℝ)+2 ≤ c*s/2)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hκdeg : ∀ u : L, ((Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, G.Adj u v ∧ G.Adj u' v)).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkB : k ≤ B) (hkn : k ≤ n)
    (hp : 4*κ*((k : ℝ)/n)^c < 1) :
    ∃ R : BleF0 n D B →ₗ[ZMod 2] MvPolynomial (Fin n×Fin D) (ZMod 2),
      IsPseudoRedF0 (representation G ι).axioms R ∧
      (1-(Fintype.card L : ℝ)*((k : ℝ)/n)^c/(1-4*κ*((k : ℝ)/n)^c))*(n.choose k : ℝ)*(D : ℝ)^k ≤
        (rankLeF0 R k : ℝ) := by
  classical
  let P := representation G ι
  have hml := multilinear G ι
  have hresp := P2MPaddedPHPRespectfulness.respectful G ι
  have hzero : ∃ y : Fin n×Fin D → Bool, ∀ g∈P.F0, eval (toF2 y) g=0 := by
    refine ⟨fun _ => false,?_⟩
    rintro g ⟨i,j,j',hne,rfl⟩
    simp [toF2]
  have hF : ∀ p∈P.axioms, p∈Ble (Fin n×Fin D) B := by
    intro p hp
    exact (mem_Ble_iff B p).mpr ⟨hml p hp,((degrees G ι δ hδ) p hp).trans hdB⟩
  have hFK : ∀ p∈P.axioms, p.totalDegree ≤ B+1 := by
    intro p hp
    exact (((mem_Ble_iff B p).mp (hF p hp)).2).trans (Nat.le_succ B)
  have hK : ((B+1 : ℕ) : ℝ)+1 ≤ c*s/2 := by push_cast; linarith
  have hExp : IsBdryExp P.graph s c := by simpa only [P,graph_eq] using hexp
  obtain ⟨R,hR,hRdeg,hRt,hRank,hOne⟩ := lemma_5_3_expansion_pseudo_reduction P MonomialOrder.degLex
    P2MDegreeLexCompatibility.compatible hml hzero hresp s c hs hc hExp (B+1) hFK hK
  let R' := P2MDivisionPseudoReductionDescent.reduction R (Nat.le_succ B)
  have hF0 : P2MDivisionPolynomialRepresentative.background n D⊆P.axioms := fun p hp => Or.inl hp
  have hPseudo : IsPseudoRedF0 P.axioms R' := P2MDivisionPseudoReductionDescent.pseudo P.axioms hF0 hF R hR
  refine ⟨R',hPseudo,?_⟩
  have hcl : ∀ v : Fin n, (Finset.univ.filter (fun x => P.cluster x=v)).card=D := by
    intro v
    have he : Finset.univ.filter (fun x : Fin n×Fin D => P.cluster x=v)=({v} : Finset (Fin n))×ˢFinset.univ := by
      ext ⟨i,j⟩
      simp [P,representation,eq_comm]
    rw [he]
    simp
  have hirr : ∀ t : Finset (Fin n×Fin D),
      (∀ x∈t, ∀ y∈t, P.cluster x=P.cluster y → x=y) → IsIrred MonomialOrder.degLex P.F0 t := by
    intro t ht
    apply P2MDivisionBackgroundStandard.irreducible
    intro i j j' hj hj'
    exact congrArg Prod.snd (ht (i,j) hj (i,j') hj' rfl)
  have hκP : ∀ u : L, ((Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card : ℝ) ≤ κ := by
    simpa only [P,graph_eq] using hκdeg
  have hRk : rankLeF0 R' k=expRank P MonomialOrder.degLex s k := by
    rw [P2MDivisionPseudoReductionDescent.rank_eq P.axioms hF0 R hR (Nat.le_succ B) k hkB]
    exact hRank k (hkB.trans (Nat.le_succ B))
  rw [hRk]
  have hb := (theorem_5_4_rank_from_expansion P MonomialOrder.degLex P2MDegreeLexCompatibility.compatible
    hml hzero hresp s c hExp (B+1) hFK (by push_cast; linarith) D hD hcl hirr κ hκ (by
      intro u
      convert hκP u using 1
      congr 1
      congr 1
      exact Finset.filter_congr_decidable _ _ _) k hk
    (hkB.trans (Nat.le_succ B)) (by simpa using hkn) (by simpa using hp)).1
  simpa only [Fintype.card_fin] using hb

end SemAC02.Supplement.P2MPaddedPHPOperatorWitness
end

section
-- Inlined Solutions.P2MGraphPHPRankLoss

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPRankLoss

 theorem small_power (n k Δ : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hp : (k : ℝ)/n ≤ 1/64) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) :
    ((k : ℝ)/n)^((Δ : ℝ)/4) ≤ 1/(n : ℝ)^3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0 < k by omega)
  have hpR : (0 : ℝ)<(k : ℝ)/n := div_pos hkR hnR
  have hlogp : Real.log ((k : ℝ)/n) ≤ -1/2 := by
    have hh := Real.log_le_sub_one_of_pos hpR
    linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have he : Real.exp (-(3*Real.log (n : ℝ)))=1/(n : ℝ)^3 := by
    have hpw : Real.exp (3*Real.log (n : ℝ))=(n : ℝ)^3 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hnR] using Real.exp_nat_mul (Real.log (n : ℝ)) 3
    rw [Real.exp_neg,hpw,one_div]
  rw [Real.rpow_def_of_pos hpR,←he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hlogp (show (0 : ℝ) ≤ (Δ : ℝ)/4 by positivity)
  nlinarith

 theorem retained_fraction (n k Δ : ℕ) (hn : 128 ≤ n) (hk : 1 ≤ k)
    (hp : (k : ℝ)/n ≤ 1/64) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) (hΔn : Δ ≤ n) :
    4*(8*(Δ : ℝ)^2)*((k : ℝ)/n)^((Δ : ℝ)/4) < 1 ∧
      1/2 ≤ 1-(2*(n : ℝ))*((k : ℝ)/n)^((Δ : ℝ)/4)/
        (1-4*(8*(Δ : ℝ)^2)*((k : ℝ)/n)^((Δ : ℝ)/4)) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hDn : (Δ : ℝ) ≤ n := by exact_mod_cast hΔn
  let q := ((k : ℝ)/n)^((Δ : ℝ)/4)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hq := small_power n k Δ (by omega) hk hp hΔ
  have hqn : (n : ℝ)^3*q ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ (n : ℝ)^3 by positivity)
    have he : (n : ℝ)^3*(1/(n : ℝ)^3)=1 := by field_simp
    rwa [he] at hh
  have hn2 : (n : ℝ)^2 ≤ (n : ℝ)^3 := by nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (show 0 ≤ (n : ℝ)-1 by linarith)]
  have hnq : (n : ℝ)^2*q ≤ 1 := (mul_le_mul_of_nonneg_right hn2 hq0).trans hqn
  have hsmall : 8*(Δ : ℝ)^2*q ≤ 1/16 := by
    have hsq : (Δ : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hDn 2
    have hdq := mul_le_mul_of_nonneg_right hsq hq0
    have hnq' : (n : ℝ)*((n : ℝ)^2*q) ≤ 1 := by nlinarith [hqn]
    have h16 : (16 : ℝ)*8*(Δ : ℝ)^2*q ≤ (n : ℝ)*((n : ℝ)^2*q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hn128) (show 0 ≤ (n : ℝ)^2*q by positivity)]
    linarith
  have hnum : 2*(n : ℝ)*q ≤ 1/8 := by
    have hnn : (16 : ℝ)*(n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hnn hq0
    nlinarith
  have hden : 0 < 1-4*(8*(Δ : ℝ)^2)*q := by nlinarith
  refine ⟨by nlinarith,?_⟩
  have hh : (2*(n : ℝ))*q/(1-4*(8*(Δ : ℝ)^2)*q) ≤ 1/2 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

end SemAC02.Supplement.P2MGraphPHPRankLoss
end

section
-- Inlined Solutions.P2MBottomWidthDivisionParameters

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MBottomWidthDivisionParameters

theorem quotient_lower (k w : ℕ) (hw : 1 ≤ w) (hwk : 2*w ≤ k) :
    (k : ℝ)/(2*w) ≤ (k/w : ℕ) := by
  have hw0 : 0 < w := by omega
  have hr : 1 ≤ k/w := (Nat.le_div_iff_mul_le hw0).mpr (by omega)
  have hmod := Nat.mod_lt k hw0
  have hdecomp : (k/w)*w+k%w=k := by simpa only [Nat.mul_comm w (k/w)] using Nat.div_add_mod k w
  have hwr : w ≤ (k/w)*w := by simpa using Nat.mul_le_mul_right w hr
  have hnat : k ≤ 2*((k/w)*w) := by omega
  have hreal : (k : ℝ) ≤ 2*(((k/w : ℕ) : ℝ)*(w : ℝ)) := by exact_mod_cast hnat
  have hwR : (0 : ℝ)<w := by exact_mod_cast hw0
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*w)).mpr
  nlinarith

theorem exponent_lower (η : ℝ) (hη : 0 < η) (n k w : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hwk : 2*w ≤ k) (hk : η*n/128 ≤ (k : ℝ)) :
    (η/1024)*(n : ℝ)/(w*(256/η)^w) ≤
      ((k/w : ℕ) : ℝ)/4*((k : ℝ)/(2*n))^w := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hwR : (0 : ℝ)<w := by exact_mod_cast (show 0 < w by omega)
  have hp : η/256 ≤ (k : ℝ)/(2*n) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*n)).mpr
    nlinarith
  have hr := quotient_lower k w hw hwk
  have hrl : η*n/(256*w) ≤ ((k/w : ℕ) : ℝ) := by
    apply le_trans _ hr
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<256*w) (by positivity : (0 : ℝ)<2*w)).mpr
    nlinarith
  calc
    _ = (η*n/(256*w))/4*(η/256)^w := by
      rw [show 256/η=(η/256)⁻¹ by field_simp]
      rw [inv_pow]
      field_simp
      ring
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hrl (by norm_num))
      (pow_le_pow_left₀ (by positivity) hp w) (by positivity) (by positivity)

end SemAC02.Supplement.P2MBottomWidthDivisionParameters
end

section
-- Inlined Solutions.P2MGraphPHPExponentComparison

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPExponentComparison

 theorem lower (n k w Δ : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w) (hΔ : 1 ≤ Δ)
    (hwk : 2*w ≤ k) (hk : (n : ℝ)/(8192*Δ) ≤ k) :
    (1/65536 : ℝ)*n/(w*Δ*(65536*(Δ : ℝ)^2)^w) ≤
      ((k/w : ℕ) : ℝ)/4*((k : ℝ)/(2*((n : ℝ)*(4*Δ))))^w := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hwR : (0 : ℝ)<w := by exact_mod_cast (show 0 < w by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hp : 1/(65536*(Δ : ℝ)^2) ≤ (k : ℝ)/(2*((n : ℝ)*(4*Δ))) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*((n : ℝ)*(4*Δ)))).mpr
    have he : (1/(65536*(Δ : ℝ)^2))*(2*((n : ℝ)*(4*Δ)))=(n : ℝ)/(8192*Δ) := by field_simp; ring
    rw [he]
    exact hk
  have hr := P2MBottomWidthDivisionParameters.quotient_lower k w hw hwk
  have hrl : (n : ℝ)/(16384*w*Δ) ≤ ((k/w : ℕ) : ℝ) := by
    apply le_trans _ hr
    have hh := div_le_div_of_nonneg_right hk (show (0 : ℝ) ≤ 2*w by positivity)
    have he : ((n : ℝ)/(8192*Δ))/(2*w)=(n : ℝ)/(16384*w*Δ) := by field_simp; ring
    rwa [he] at hh
  calc
    _ = ((n : ℝ)/(16384*w*Δ))/4*(1/(65536*(Δ : ℝ)^2))^w := by
      simp only [one_div,inv_pow]
      field_simp <;> ring
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hrl (by norm_num))
      (pow_le_pow_left₀ (by positivity) hp w) (by positivity) (by positivity)

end SemAC02.Supplement.P2MGraphPHPExponentComparison
end

section
-- Inlined Solutions.P2MBipartiteIntersectionDegree

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MBipartiteIntersectionDegree

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

end P2MProofComplexity.P2MBipartiteIntersectionDegree
end

section
-- Inlined Solutions.P2MGraphPHPDeterministicBound

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphPHPDeterministicBound

open MvPolynomial ACirc AC02Frege P2MPaddedPHPRepresentation

 theorem lower_bound (n Δ k s : ℕ) (hn : 128 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hlog : 24*Real.log n ≤ (Δ : ℝ)) (hk : 1 ≤ k) (hΔk : 2*Δ ≤ k) (hkn : 6*k ≤ n)
    (hs : 1 ≤ s) (hbudget : ((6*k : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*s/8)
    (hkL : (n : ℝ)/(8192*Δ) ≤ k) (hp : (k : ℝ)/n ≤ 1/64)
    (G : PCNonBool.BipGraph (Fin (2*n)) (Fin n))
    (hExp : IsBdryExp G s ((Δ : ℝ)/4))
    (hL : ∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ 2*Δ)
    (hR : ∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ 4*Δ)
    (w : ℕ) (hw : 1 ≤ w) (hwΔ : w ≤ Δ)
    (ι : ∀ v : Fin n, {u : Fin (2*n) // G.Adj u v} ↪ Fin (4*Δ))
    (π : List (ACirc (ZMod 2) (Fin n×Fin (4*Δ))))
    (hπ : IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4*Δ)) (polyAx (phpPadded G ι)) π) :
    1/4*Real.exp ((1/65536 : ℝ)*n/(w*Δ*(65536*(Δ : ℝ)^2)^w)) ≤
      topS (nDivOmega n (4*Δ)) π := by
  classical
  let P := representation G ι
  let r := k/w
  let B := 3*(k+max (2*Δ) (r*w))
  have hrw : r*w ≤ k := Nat.div_mul_le_self k w
  have hwk : 2*w ≤ k := (Nat.mul_le_mul_left 2 hwΔ).trans hΔk
  have hB6 : B ≤ 6*k := by dsimp [B]; omega
  have hkB : k ≤ B := by dsimp [B]; omega
  have hBN : B ≤ n := hB6.trans hkn
  have hdB : max 2 (2*Δ) ≤ B := by dsimp [B]; omega
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hBudget : (B : ℝ)+2 ≤ ((Δ : ℝ)/4)*s/2 := by
    have hh : (B : ℝ) ≤ ((6*k : ℕ) : ℝ) := by exact_mod_cast hB6
    nlinarith
  have hκNat : max 1 ((2*Δ)*(4*Δ-1)) ≤ 8*Δ^2 := by
    apply max_le
    · nlinarith
    · have hh := Nat.mul_le_mul_left (2*Δ) (Nat.sub_le (4*Δ) 1)
      nlinarith
  have hκdeg : ∀ u, ((Finset.univ.filter (fun u' => u'≠u ∧ ∃ v, G.Adj u v ∧ G.Adj u' v)).card : ℝ) ≤ 8*(Δ : ℝ)^2 := by
    intro u
    have hh := (P2MProofComplexity.P2MBipartiteIntersectionDegree.bound G (2*Δ) (4*Δ) hL hR u).trans hκNat
    exact_mod_cast hh
  have hret := P2MGraphPHPRankLoss.retained_fraction n k Δ hn hk hp hlog hΔn
  obtain ⟨R,hPseudo,hRank⟩ := P2MPaddedPHPOperatorWitness.exists_reduction G ι (by omega) (2*Δ) hL
    s ((Δ : ℝ)/4) (by exact_mod_cast hs) (by positivity) hExp B hdB hBudget
    (8*(Δ : ℝ)^2) (by
      have hh : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
      nlinarith)
    hκdeg k hk hkB (by omega) hret.1
  have hRankHalf : (1/2 : ℝ)*(n.choose k : ℝ)*(4*Δ : ℕ)^k ≤ rankLeF0 R k := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hret.2 (Nat.cast_nonneg (n.choose k)))
      (show (0 : ℝ) ≤ ((4*Δ : ℕ) : ℝ)^k by positivity)
    have hb : (1-(2*(n : ℝ))*((k : ℝ)/n)^((Δ : ℝ)/4)/(1-4*(8*(Δ : ℝ)^2)*((k : ℝ)/n)^((Δ : ℝ)/4)))*
        (n.choose k : ℝ)*((4*Δ : ℕ) : ℝ)^k ≤ rankLeF0 R k := by
      simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hRank
    exact hh.trans hb
  have hdiv : ∀ (i : Fin n) (j j' : Fin (4*Δ)), j≠j' → X (i,j)*X (i,j')∈P.axioms :=
    fun i j j' hne => Or.inl ⟨i,j,j',hne,rfl⟩
  have hdegree : ∀ p∈P.axioms, restrOmega n (4*Δ) p∈BleF0 n (4*Δ) (2*Δ) := by
    intro p hp
    refine ⟨p,(mem_restrictTotalDegree _ _ _).mpr ?_,rfl⟩
    have hh := degrees G ι (2*Δ) hL p hp
    simpa only [max_eq_right (by omega : 2 ≤ 2*Δ)] using hh
  have hπP : IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4*Δ)) (polyAx P.axioms) π := by
    dsimp only [P]
    rw [encoded_axioms]
    exact hπ
  have hb := theorem_4_5_spsp_rank_bound P.axioms hdiv (2*Δ) hdegree w k r hw hwk (by omega)
    hBN R hPseudo π hπP
  have hDen : (0 : ℝ)<2*(n.choose k : ℝ)*((4*Δ : ℕ) : ℝ)^k := by
    have hc : (0 : ℝ)<(n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
    positivity
  have hQuarter : (1/4 : ℝ) ≤ (rankLeF0 R k : ℝ)/(2*(n.choose k : ℝ)*((4*Δ : ℕ) : ℝ)^k) :=
    (le_div_iff₀ hDen).mpr (by nlinarith)
  have hExponent := P2MGraphPHPExponentComparison.lower n k w Δ (by omega) hw hΔ hwk hkL
  apply le_trans _ hb
  have hh := mul_le_mul hQuarter (Real.exp_le_exp.mpr hExponent) (Real.exp_pos _).le (by positivity)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

end SemAC02.Supplement.P2MGraphPHPDeterministicBound
end

section
-- Inlined Solutions.P2MGraphPHPParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPParameters

noncomputable def degree (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4096*Δ)⌋₊
noncomputable def supportSize (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4*Δ)⌋₊

 theorem finite_data (n Δ : ℕ) (hn : 128 ≤ n) (hΔ : 1 ≤ Δ)
    (hlarge : 32768*(Δ : ℝ)^2 ≤ n) :
    Δ ≤ n ∧ 1 ≤ degree n Δ ∧ 2*Δ ≤ degree n Δ ∧ 6*degree n Δ ≤ n ∧
      1 ≤ supportSize n Δ ∧ ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 ∧
      (n : ℝ)/(8192*Δ) ≤ degree n Δ ∧ (degree n Δ : ℝ)/n ≤ 1/64 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔSmall : (Δ : ℝ) ≤ (n : ℝ)/128 := by nlinarith [sq_nonneg ((Δ : ℝ)-1)]
  have hDiv : 4*(Δ : ℝ) ≤ (n : ℝ)/(8192*Δ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ)<8192*Δ)).mpr (by nlinarith)
  have hkU : (degree n Δ : ℝ) ≤ (n : ℝ)/(4096*Δ) := Nat.floor_le (by positivity)
  have hkf : (n : ℝ)/(4096*Δ)-1 < (degree n Δ : ℝ) := Nat.sub_one_lt_floor _
  have he : (n : ℝ)/(4096*Δ)=2*((n : ℝ)/(8192*Δ)) := by ring
  have hkL : (n : ℝ)/(8192*Δ) ≤ degree n Δ := by rw [he] at hkf; nlinarith
  have hk2Δ : 2*Δ ≤ degree n Δ := by
    have hh : (2 : ℝ)*Δ ≤ degree n Δ := by linarith
    exact_mod_cast hh
  have hk1 : 1 ≤ degree n Δ := by omega
  have hkMult := (le_div_iff₀ (show (0 : ℝ)<4096*Δ by positivity)).mp hkU
  have hΔk : (degree n Δ : ℝ) ≤ (Δ : ℝ)*(degree n Δ : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (Δ : ℝ)-1 by linarith) (Nat.cast_nonneg (α:=ℝ) (degree n Δ))]
  have hkUn : (degree n Δ : ℝ) ≤ (n : ℝ)/4096 := by nlinarith
  have hk6 : 6*degree n Δ ≤ n := by
    have hh : (6 : ℝ)*(degree n Δ : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hsL : (n : ℝ)/4-Δ ≤ (Δ : ℝ)*supportSize n Δ := by
    have hf : (n : ℝ)/(4*Δ)-1 < (supportSize n Δ : ℝ) := Nat.sub_one_lt_floor _
    have hh := mul_lt_mul_of_pos_left hf hΔR
    have he : (Δ : ℝ)*((n : ℝ)/(4*Δ)-1)=(n : ℝ)/4-Δ := by field_simp <;> ring
    rw [he] at hh
    exact hh.le
  have hbudget : ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 := by
    push_cast
    nlinarith
  have hs1 : 1 ≤ supportSize n Δ := by
    by_contra hh
    have hz : supportSize n Δ=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero,zero_div] at hbudget
    have hk0 := Nat.cast_nonneg (α:=ℝ) (6*degree n Δ)
    linarith
  have hDn : Δ ≤ n := by
    have hh : (Δ : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  have hp : (degree n Δ : ℝ)/n ≤ 1/64 := (div_le_iff₀ hnR).mpr (by nlinarith)
  exact ⟨hDn,hk1,hk2Δ,hk6,hs1,hbudget,hkL,hp⟩

end SemAC02.Supplement.P2MGraphPHPParameters
end

section
-- Inlined Solutions.P2MLogGrowth

open Filter Topology

namespace P2MProofComplexity.P2MLogGrowth

theorem eventually_log_large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop b

theorem eventually_log_power_le (A : ℝ) (k : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, A*(Real.log (n : ℝ))^k ≤ (n : ℝ)^C := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hC).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hb := (h.const_mul_left A).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with n hn
  have he : |A*(Real.log (n : ℝ))^k| ≤ (n : ℝ)^C := by
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) C)] using hn
  exact (le_abs_self _).trans he

theorem eventually_scaled_power_le (A p q : ℝ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, A*(n : ℝ)^p ≤ (n : ℝ)^q := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < q-p)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop A
  filter_upwards [hlarge,eventually_ge_atTop 1] with n hn hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ)^(q-p)*(n : ℝ)^p := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ)^((q-p)+p) := (Real.rpow_add hnp _ _).symm
    _ = _ := by congr 1; ring

end P2MProofComplexity.P2MLogGrowth
end

section
-- Inlined Solutions.P2MGraphPHPAsymptoticParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPAsymptoticParameters

open Filter

 theorem eventual_data : ∀ᶠ n : ℕ in atTop,
    128 ≤ n ∧ 1 ≤ php74Delta n ∧ 24*Real.log n ≤ (php74Delta n : ℝ) ∧
      1 ≤ Real.log n ∧ 1 ≤ Real.log (Real.log n) ∧
      php74Delta n ≤ n ∧ 1 ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      2*php74Delta n ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      6*P2MGraphPHPParameters.degree n (php74Delta n) ≤ n ∧
      1 ≤ P2MGraphPHPParameters.supportSize n (php74Delta n) ∧
      ((6*P2MGraphPHPParameters.degree n (php74Delta n) : ℕ) : ℝ)+2 ≤
        (php74Delta n : ℝ)*(P2MGraphPHPParameters.supportSize n (php74Delta n))/8 ∧
      (n : ℝ)/(8192*php74Delta n) ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      (P2MGraphPHPParameters.degree n (php74Delta n) : ℝ)/n ≤ 1/64 := by
  have hgrowth := P2MProofComplexity.P2MLogGrowth.eventually_log_power_le (32768*49^2) 2 (C:=1) (by norm_num)
  have hlog := P2MProofComplexity.P2MLogGrowth.eventually_log_large 1
  have hloglog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop 1
  filter_upwards [hgrowth,hlog,hloglog,eventually_ge_atTop 128] with n hg hl hll hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have hsum : Real.log (2*(n : ℝ))=Real.log 2+Real.log n := Real.log_mul (by norm_num) hnR.ne'
  have hLower : 24*Real.log n ≤ (php74Delta n : ℝ) := by
    have hh := Nat.le_ceil (24*Real.log (2*(n : ℝ)))
    rw [hsum] at hh
    change 24*Real.log n ≤ (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ)
    rw [hsum]
    linarith
  have hD1 : 1 ≤ php74Delta n := by
    have hh : (1 : ℝ) ≤ php74Delta n := by linarith
    exact_mod_cast hh
  have hUpper : (php74Delta n : ℝ) ≤ 49*Real.log n := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 24*Real.log (2*(n : ℝ)) by rw [hsum]; positivity)
    change (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ) ≤ 49*Real.log n
    rw [hsum] at hh ⊢
    linarith
  have hlarge : 32768*(php74Delta n : ℝ)^2 ≤ n := by
    simp only [Real.rpow_one] at hg
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (php74Delta n)) hUpper 2
    nlinarith
  rcases P2MGraphPHPParameters.finite_data n (php74Delta n) hn hD1 hlarge with
    ⟨hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩
  exact ⟨hn,hD1,hLower,hl,hll,hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩

 theorem width_bound (n w : ℕ) (hl : 1 ≤ Real.log n) (hll : 1 ≤ Real.log (Real.log n))
    (hD : 24*Real.log n ≤ (php74Delta n : ℝ))
    (hw : (w : ℝ) ≤ Real.log n/Real.log (Real.log n)) : w ≤ php74Delta n := by
  have hh : Real.log n/Real.log (Real.log n) ≤ Real.log n := div_le_self (by linarith) hll
  have hwr : (w : ℝ) ≤ php74Delta n := by linarith
  exact_mod_cast hwr

end SemAC02.Supplement.P2MGraphPHPAsymptoticParameters
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
-- Inlined Solutions.P2MArithmeticVariableRename

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MArithmeticVariableRename

open ACirc P2MArithmeticCircuitBasics

noncomputable def circuit {F V U : Type} (f : V → U) : ACirc F V → ACirc F U
  | .var i => .var (f i)
  | .const a => .const a
  | .sum ps => .sum (ps.attach.map (fun p => (p.1.1,circuit f p.1.2)))
  | .prod cs => .prod (cs.attach.map (fun c => circuit f c.1))
termination_by c => c
decreasing_by
  all_goals first
    | (obtain ⟨⟨a,b⟩,hp⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (obtain ⟨c,hc⟩ := c; have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem circuit_sum {F V U : Type} (f : V → U) (ps : List (F×ACirc F V)) :
    circuit f (.sum ps)=.sum (ps.map (fun p => (p.1,circuit f p.2))) := by
  rw [circuit,List.attach_map_val (f:=fun p : F×ACirc F V => (p.1,circuit f p.2))]

theorem circuit_prod {F V U : Type} (f : V → U) (cs : List (ACirc F V)) :
    circuit f (.prod cs)=.prod (cs.map (circuit f)) := by
  rw [circuit,List.attach_map_val]

theorem value {F V U : Type} [CommRing F] (f : V → U) (c : ACirc F V) (y : U → Bool) :
    cval (circuit f c) y=cval c (fun i => y (f i)) := by
  cases c with
  | var i => simp [circuit,cval,polyFn,toPoly,boolPt]
  | const a => simp [circuit,cval,polyFn,toPoly]
  | sum ps =>
    rw [circuit_sum,cval_sum,cval_sum,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    dsimp only [Function.comp_def]
    rw [value f p.2 y]
  | prod cs =>
    rw [circuit_prod,cval_prod,cval_prod,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact value f c y
termination_by c
decreasing_by
  all_goals first
    | (obtain ⟨a,b⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

theorem leaf {F V U : Type} (f : V → U) (c : ACirc F V) (hc : IsLeaf c) : IsLeaf (circuit f c) := by
  cases c <;> simp_all [IsLeaf,circuit]

theorem sum_of {F V U : Type} (f : V → U) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsSumOf P c) : IsSumOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | prod cs => exact hc.elim
  | sum ps =>
    rw [circuit_sum]
    rintro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hPQ q.2 (hc q hq)

theorem prod_of {F V U : Type} (f : V → U) (P : ACirc F V → Prop) (Q : ACirc F U → Prop)
    (hPQ : ∀ c, P c → Q (circuit f c)) (c : ACirc F V) (hc : IsProdOf P c) : IsProdOf Q (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    intro d hd
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
    exact hPQ c (hc c hc')

theorem monomial {F V U : Type} (f : V → U) (w : ℕ∞) (c : ACirc F V) (hc : IsMonGate w c) :
    IsMonGate w (circuit f c) := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs =>
    rw [circuit_prod]
    constructor
    · simpa only [List.length_map] using hc.1
    · intro d hd
      obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hd
      exact leaf f c (hc.2 c hc')

theorem spsp {F V U : Type} (f : V → U) (w : ℕ∞) (c : ACirc F V) (hc : IsSPSP w c) :
    IsSPSP w (circuit f c) :=
  sum_of f _ _ (prod_of f _ _ (sum_of f _ _ (monomial f w))) c hc

theorem top_terms {F V U : Type} (f : V → U) (c : ACirc F V) :
    topTerms (circuit f c)=(topTerms c).map (circuit f) := by
  cases c <;> simp [circuit,circuit_sum,circuit_prod,topTerms,List.map_map,Function.comp_def]

end SemAC02.Supplement.P2MArithmeticVariableRename
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
-- Inlined Solutions.P2MArithmeticRefutationRename

set_option maxHeartbeats 1000000

namespace SemAC02.Supplement.P2MArithmeticRefutationRename

open ACirc P2MArithmeticVariableRename MvPolynomial

theorem refutation {F V U : Type} [Field F] (f : V → U) (w : ℕ∞)
    (S : Set (MvPolynomial V F)) (π : List (ACirc F V))
    (hπ : IsSemPCRef (IsSPSP w) Set.univ (polyAx S) π) (Ω : Set (U → Bool)) :
    IsSemPCRef (IsSPSP w) Ω (polyAx (rename f '' S)) (π.map (circuit f)) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact spsp f w a (hπ.1 a ha)
  · intro i hi
    have hi' : i < π.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map]
    rcases hπ.2.1 i hi' with ⟨a,ha,he⟩ | he | ⟨j,l,hj,hl,he⟩
    · obtain ⟨p,hp,rfl⟩ := ha
      left
      refine ⟨polyFn (rename f p),⟨rename f p,⟨p,hp,rfl⟩,rfl⟩,?_⟩
      intro x hx
      rw [value,he _ (Set.mem_univ _)]
      simp only [polyFn,eval_rename]
      congr 1
    · right; left
      intro x hx
      rw [value]
      exact he _ (Set.mem_univ _)
    · right; right
      refine ⟨j,l,hj,hl,?_⟩
      intro x hx hp hq
      rw [value] at hp hq ⊢
      exact he _ (Set.mem_univ _) hp hq
  · obtain ⟨c,hc,hval⟩ := hπ.2.2
    refine ⟨circuit f c,?_,?_⟩
    · rw [List.getLast?_map,hc]; rfl
    · intro x hx
      rw [value]
      exact hval _ (Set.mem_univ _)

theorem top_bound {F V U : Type} [CommRing F] (f : V → U) (π : List (ACirc F V)) :
    topS Set.univ (π.map (circuit f)) ≤ topS Set.univ π := by
  apply P2MProofTopFunctions.projection_bound (fun x => fun i => x (f i)) (circuit f) (circuit f) π (top_terms f)
  intro c hc t ht x
  exact value f t x

theorem domain_top_bound {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ topS Set.univ π := by
  classical
  let pull (g : ↥(Set.univ : Set (V → Bool)) → F) : Ω → F := fun x => g ⟨x.1,Set.mem_univ _⟩
  have hsub : P2MProofTopFunctions.pool Ω π⊆(P2MProofTopFunctions.pool Set.univ π).image pull := by
    intro g hg
    obtain ⟨hn,c,hc,t,ht,he⟩ := (P2MProofTopFunctions.mem_pool Ω π g).mp hg
    let a : ↥(Set.univ : Set (V → Bool)) → F := fun x => cval t x.1
    have ha : pull a=g := by rw [←he]
    have hn' : a≠0 := by intro hz; apply hn; rw [←ha,hz]; rfl
    exact Finset.mem_image.mpr ⟨a,(P2MProofTopFunctions.mem_pool Set.univ π a).mpr ⟨hn',c,hc,t,ht,rfl⟩,ha⟩
  rw [←P2MProofTopFunctions.card_eq_topS,←P2MProofTopFunctions.card_eq_topS]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end SemAC02.Supplement.P2MArithmeticRefutationRename
end

section
-- Inlined Solutions.P2MGraphPHPToPadded

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPToPadded

open MvPolynomial ACirc

 theorem embeddings_exist {L : Type} [Fintype L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (hR : ∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ D) :
    Nonempty (∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) := by
  classical
  have he : ∀ v : Fin n, Nonempty ({u : L // G.Adj u v} ↪ Fin D) := by
    intro v
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin,Fintype.card_subtype] using hR v
  exact ⟨fun v => Classical.choice (he v)⟩

noncomputable def placement {L : Type} {n D : ℕ} (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (e : Edge G) : Fin n×Fin D :=
  (e.1.2,ι e.1.2 ⟨e.1.1,e.2⟩)

 theorem axioms_subset {L : Type} [Fintype L] [DecidableEq L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) :
    rename (placement G ι) '' phpG G⊆phpPadded G ι := by
  classical
  rintro p ⟨q,(⟨u,rfl⟩ | ⟨u,u',v,h,h',hne,rfl⟩),rfl⟩
  · right
    refine ⟨u,?_⟩
    simp only [map_prod,map_sub,map_one,xE,rename_X,placement]
  · left
    refine ⟨v,ι v ⟨u,h⟩,ι v ⟨u',h'⟩,?_,?_⟩
    · intro he
      exact hne (congrArg Subtype.val ((ι v).injective he))
    · simp only [map_mul,xE,rename_X,placement]

 theorem refutation {L : Type} [Fintype L] [DecidableEq L] {n D : ℕ}
    (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (w : ℕ∞)
    (π : List (ACirc (ZMod 2) (Edge G)))
    (hπ : IsSemPCRef (IsSPSP w) Set.univ (polyAx (phpG G)) π) :
    IsSemPCRef (IsSPSP w) (nDivOmega n D) (polyAx (phpPadded G ι))
      (π.map (P2MArithmeticVariableRename.circuit (placement G ι))) := by
  have hh := P2MArithmeticRefutationRename.refutation (placement G ι) w (phpG G) π hπ (nDivOmega n D)
  refine ⟨hh.1,?_,hh.2.2⟩
  intro k hk
  rcases hh.2.1 k hk with ⟨a,ha,he⟩ | hz | hs
  · left
    refine ⟨a,?_,he⟩
    obtain ⟨p,hp,rfl⟩ := ha
    exact ⟨p,axioms_subset G ι hp,rfl⟩
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr hs)

 theorem top_bound {L : Type} {n D : ℕ} (G : PCNonBool.BipGraph L (Fin n))
    (ι : ∀ v : Fin n, {u : L // G.Adj u v} ↪ Fin D) (π : List (ACirc (ZMod 2) (Edge G))) :
    topS (nDivOmega n D) (π.map (P2MArithmeticVariableRename.circuit (placement G ι))) ≤ topS Set.univ π :=
  (P2MArithmeticRefutationRename.domain_top_bound _ _).trans (P2MArithmeticRefutationRename.top_bound _ _)

end SemAC02.Supplement.P2MGraphPHPToPadded
end

section
-- Inlined Solutions.P2MGraphPHPBoundedBottom

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MGraphPHPBoundedBottom

open ACirc Filter

theorem full :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (2 * n)) (Fin n), Lemma74Concl G →
      ∀ w : ℕ, 1 ≤ w → (w : ℝ) ≤ Real.log n / Real.log (Real.log n) →
        (∀ π : List (ACirc (ZMod 2) (Edge G)),
          IsSemPCRef (IsSPSP (w : ℕ∞)) Set.univ (polyAx (phpG G)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS Set.univ π) ∧
        (∀ (ι : ∀ v : Fin n, {u : Fin (2 * n) // G.Adj u v} ↪ Fin (4 * php74Delta n))
          (π : List (ACirc (ZMod 2) (Fin n × Fin (4 * php74Delta n)))),
          IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4 * php74Delta n))
            (polyAx (phpPadded G ι)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS (nDivOmega n (4 * php74Delta n)) π)  := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp P2MGraphPHPAsymptoticParameters.eventual_data
  refine ⟨1/65536,65536,by norm_num,by norm_num,n₀,?_⟩
  intro n hn G hG w hw hwRange
  rcases hn₀ n hn with ⟨hn128,hΔ,hΔlog,hlog,hloglog,hΔn,hk,hΔk,hkn,hs,hBudget,hkL,hp⟩
  have hwΔ := P2MGraphPHPAsymptoticParameters.width_bound n w hlog hloglog hΔlog hwRange
  have hExp : IsBdryExp G (P2MGraphPHPParameters.supportSize n (php74Delta n)) ((php74Delta n : ℝ)/4) := by
    simpa only [P2MGraphPHPParameters.supportSize] using hG.1
  have hPadded : ∀
      (ι : ∀ v : Fin n, {u : Fin (2*n) // G.Adj u v} ↪ Fin (4*php74Delta n))
      (π : List (ACirc (ZMod 2) (Fin n×Fin (4*php74Delta n)))),
      IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4*php74Delta n)) (polyAx (phpPadded G ι)) π →
        1/4*Real.exp ((1/65536 : ℝ)*n/(w*php74Delta n*(65536*(php74Delta n : ℝ)^2)^w)) ≤
          topS (nDivOmega n (4*php74Delta n)) π := by
    intro ι π hπ
    exact P2MGraphPHPDeterministicBound.lower_bound n (php74Delta n)
      (P2MGraphPHPParameters.degree n (php74Delta n)) (P2MGraphPHPParameters.supportSize n (php74Delta n))
      hn128 hΔ hΔn hΔlog hk hΔk hkn hs hBudget hkL hp G hExp hG.2.1 hG.2.2 w hw hwΔ ι π hπ
  refine ⟨?_,hPadded⟩
  intro π hπ
  obtain ⟨ι⟩ := P2MGraphPHPToPadded.embeddings_exist G hG.2.2
  have hb := hPadded ι (π.map (P2MArithmeticVariableRename.circuit (P2MGraphPHPToPadded.placement G ι)))
    (P2MGraphPHPToPadded.refutation G ι (w : ℕ∞) π hπ)
  apply hb.trans
  exact_mod_cast P2MGraphPHPToPadded.top_bound G ι π

end SemAC02.Supplement.P2MGraphPHPBoundedBottom
end

end P2MGraphPHPBoundedBottomProof
open SemAC02.Supplement MvPolynomial ACirc Filter Topology

theorem solution :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (2 * n)) (Fin n), Lemma74Concl G →
      ∀ w : ℕ, 1 ≤ w → (w : ℝ) ≤ Real.log n / Real.log (Real.log n) →
        (∀ π : List (ACirc (ZMod 2) (Edge G)),
          IsSemPCRef (IsSPSP (w : ℕ∞)) Set.univ (polyAx (phpG G)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS Set.univ π) ∧
        (∀ (ι : ∀ v : Fin n, {u : Fin (2 * n) // G.Adj u v} ↪ Fin (4 * php74Delta n))
          (π : List (ACirc (ZMod 2) (Fin n × Fin (4 * php74Delta n)))),
          IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n (4 * php74Delta n))
            (polyAx (phpPadded G ι)) π →
          1 / 4 * Real.exp (c₀ * n / (w * php74Delta n *
            (C₀ * (php74Delta n : ℝ) ^ 2) ^ w)) ≤ topS (nDivOmega n (4 * php74Delta n)) π)  := by
  exact P2MGraphPHPBoundedBottomProof.SemAC02.Supplement.P2MGraphPHPBoundedBottom.full
