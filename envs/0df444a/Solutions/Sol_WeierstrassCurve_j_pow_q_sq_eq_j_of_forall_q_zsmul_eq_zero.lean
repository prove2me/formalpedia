-- Prove2me | solution 1 for WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/28b8d57e-7bb2-56e8-bb41-8e0852fefa1c

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option Elab.async false

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero.Polynomial"

namespace Polynomial
p2m_export "Polynomial" "C separable_def expand_expand X card_roots' eval_mul derivative_C C_sub natDegree_zero leadingCoeff_expand coe_aeval_eq_eval leadingCoeff coeff natDegree_expand degree_C_mul_X_le expand_C eval_map_apply natDegree_quadratic_le degree expand C_0 map_id IsRoot.def degree_sub_le Splits map mem_roots eq_zero_of_natDegree_lt_card_of_eval_eq_zero' eval_zero Monic comp roots eval_pow degree_C_le Separable natDegree eval_X eval_C nontrivial roots_expand eval_sub expand_contract natDegree_eq_of_degree_eq_some derivative_sub expand_X derivative contract eval_add isCoprime_iff_aeval_ne_zero_of_isAlgClosed nodup_roots evalEval degree_X_pow ext C_eq_zero eq_C_of_degree_le_zero IsRoot discr degree_add_eq_left_of_degree_lt ring natDegree_sub_C eval degree_zero"
p2m_open "Polynomial"

variable {F : Type*} [Field F]

theorem exists_eval_eq_of_not_separable_sub_C [IsAlgClosed F] {f : F[X]} {v : F}
    (hv : ¬ (f - C v).Separable) : ∃ a : F, (derivative f).eval a = 0 ∧ f.eval a = v := by
  rw [separable_def, derivative_sub, derivative_C, sub_zero,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed F F] at hv
  push Not at hv
  obtain ⟨a, ha, ha'⟩ := hv
  rw [coe_aeval_eq_eval] at ha ha'
  refine ⟨a, ha', ?_⟩
  rwa [eval_sub, eval_C, sub_eq_zero] at ha

theorem setOf_not_separable_sub_C_subset [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    (hf : derivative f ≠ 0) :
    {v : F | ¬ (f - C v).Separable} ⊆ ((derivative f).roots.toFinset.image fun a => f.eval a) := by
  intro v hv
  obtain ⟨a, ha, hav⟩ := exists_eval_eq_of_not_separable_sub_C hv
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset,
    mem_roots hf, IsRoot.def]
  exact ⟨a, ha, hav⟩

theorem finite_setOf_not_separable_sub_C [IsAlgClosed F] {f : F[X]} (hf : derivative f ≠ 0) :
    {v : F | ¬ (f - C v).Separable}.Finite := by
  classical
  exact (Finset.finite_toSet _).subset (setOf_not_separable_sub_C_subset hf)

theorem card_roots_toFinset_sub_C_of_separable [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    {v : F} (hsep : (f - C v).Separable) : (f - C v).roots.toFinset.card = f.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    natDegree_sub_C]

theorem exists_separable_sub_C [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    (hf : derivative f ≠ 0) {B : Set F} (hB : B.Finite) :
    ∃ v ∉ B, (f - C v).Separable ∧ (f - C v).roots.toFinset.card = f.natDegree := by
  obtain ⟨v, hv⟩ := (hB.union (finite_setOf_not_separable_sub_C hf)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact ⟨v, hv.1, hv.2, card_roots_toFinset_sub_C_of_separable hv.2⟩

theorem derivative_eq_zero_of_card_roots_sub_C_le [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    {d : ℕ} (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ d) (hd : d < f.natDegree) :
    derivative f = 0 := by
  by_contra hf
  obtain ⟨v, -, -, hcard⟩ := exists_separable_sub_C hf Set.finite_empty
  exact absurd (hcard ▸ hfib v) (not_le.mpr hd)

theorem card_roots_toFinset_expand_sub_C [DecidableEq F] (q : ℕ) [Fact q.Prime] [CharP F q]
    [PerfectRing F q] (g : F[X]) (v : F) :
    (expand F q g - C v).roots.toFinset.card = (g - C v).roots.toFinset.card := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hexp : expand F q g - C v = expand F q (g - C v) := by rw [map_sub, expand_C]
  rw [hexp, roots_expand, Multiset.toFinset_nsmul _ _ hq, Multiset.toFinset_map,
    Finset.card_image_of_injective _ (frobeniusEquiv F q).symm.injective]

theorem card_roots_contract_sub_C_le [DecidableEq F] (q : ℕ) [Fact q.Prime] [CharP F q]
    [PerfectRing F q] {f : F[X]} (hf : derivative f = 0) {d : ℕ}
    (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ d) (v : F) :
    (contract q f - C v).roots.toFinset.card ≤ d := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hfe : expand F q (contract q f) = f := expand_contract q hf hq
  rw [← card_roots_toFinset_expand_sub_C q, hfe]
  exact hfib v

theorem eq_X_pow_sq_add_C_of_card_roots_sub_C_le_two [IsAlgClosed F] [DecidableEq F] (q : ℕ)
    [hq : Fact q.Prime] [CharP F q] (hq3 : 3 ≤ q) {f : F[X]} (hmon : f.Monic)
    (hdeg : f.natDegree = q ^ 2) (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ 2) :
    ∃ β : F, f = X ^ (q ^ 2) + C β := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hqpos : 0 < q := hq.out.pos

  have hf' : derivative f = 0 :=
    derivative_eq_zero_of_card_roots_sub_C_le hfib (by rw [hdeg]; nlinarith)
  set g := contract q f with hg
  have hfg : expand F q g = f := expand_contract q hf' hq0
  have hgdeg : g.natDegree = q := by
    have h := congrArg natDegree hfg
    rw [natDegree_expand, hdeg, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right hqpos h
  have hgfib : ∀ v : F, (g - C v).roots.toFinset.card ≤ 2 :=
    card_roots_contract_sub_C_le q hf' hfib

  have hg' : derivative g = 0 :=
    derivative_eq_zero_of_card_roots_sub_C_le hgfib (by rw [hgdeg]; omega)
  set h := contract q g with hh
  have hgh : expand F q h = g := expand_contract q hg' hq0
  have hhdeg : h.natDegree = 1 := by
    have h1 := congrArg natDegree hgh
    rw [natDegree_expand, hgdeg] at h1
    exact Nat.eq_of_mul_eq_mul_right hqpos (by rw [one_mul]; exact h1)

  have hfh : expand F (q ^ 2) h = f := by rw [pow_two, ← expand_expand, hgh, hfg]
  have hhmon : h.Monic := by
    have hl := hmon.leadingCoeff
    rwa [← hfh, leadingCoeff_expand (pow_pos hqpos 2)] at hl
  obtain ⟨β, hβ⟩ : ∃ β : F, h = X + C β := ⟨h.coeff 0, hhmon.eq_X_add_C hhdeg⟩
  refine ⟨β, ?_⟩
  rw [← hfh, hβ, map_add, expand_X, expand_C]

end Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine ΨSq_zero Affine.negY variableChange_j a₃ b_relation a₁ natDegree_Φ map j_of_char_two b₂ variableChange_b₂ twoTorsionPolynomial coe_Δ' map_j Φ_two Ψ₂Sq a₄ a₂ a₆ twoTorsionPolynomial_discr_ne_zero_of_isElliptic variableChange_b₆ map_id ΨSq toAffine Affine.Point Ψ₂Sq_eq b₆ b₈ variableChange_b₄ Δ c₄ VariableChange leadingCoeff_Φ map_Ψ₂Sq j b₄ Δ' Affine.evalEval_psi_sq Psi2Sq_ne_zero_of_isElliptic"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F]

private lemma _root_.WeierstrassCurve.exists_equation_of_isAlgClosed [IsAlgClosed F] (W : WeierstrassCurve F) (x : F) :
    ∃ y : F, W.toAffine.Equation x y := by
  have hdeg : ((X : F[X]) ^ 2 + (C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    · norm_num
    · rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; decide)
  refine ⟨y, (W.toAffine.equation_iff x y).mpr ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hy
  linear_combination hy

p2m_export "WeierstrassCurve" "exists_equation_of_isAlgClosed"

private lemma _root_.WeierstrassCurve.card_le_two_of_forall_equation [DecidableEq F] (W : WeierstrassCurve F) (x : F)
    (s : Finset F) (hs : ∀ y ∈ s, W.toAffine.Equation x y) : s.card ≤ 2 := by
  set Q : F[X] := X ^ 2 + (C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) with hQ
  have hdeg : Q.degree = 2 := by
    rw [hQ, degree_add_eq_left_of_degree_lt, degree_X_pow]
    · norm_num
    · rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  have hQ0 : Q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hdeg
    exact absurd hdeg (by decide)
  have hnat : Q.natDegree = 2 := natDegree_eq_of_degree_eq_some hdeg
  have hsub : s ⊆ Q.roots.toFinset := by
    intro y hy
    have he := (W.toAffine.equation_iff x y).mp (hs y hy)
    rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, hQ]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination he
  calc s.card ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ = 2 := hnat

p2m_export "WeierstrassCurve" "card_le_two_of_forall_equation"

private theorem _root_.WeierstrassCurve.a₁_eq_zero_of_forall_two_nsmul_eq_zero [IsAlgClosed F] [DecidableEq F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0) : E.a₁ = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  by_contra ha
  obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed (E.a₃ / E.a₁)
  have h : E.toAffine.Nonsingular (E.a₃ / E.a₁) y :=
    (E.toAffine.equation_iff_nonsingular).mp hy
  have h1 : E.a₁ * (E.a₃ / E.a₁) = E.a₃ := by field_simp
  have hneg : E.toAffine.negY (E.a₃ / E.a₁) y = y := by
    rw [Affine.negY]
    linear_combination (-1 : F) * h1 + (-y - E.a₃) * h2
  have htwo : 2 • (Point.some (E.a₃ / E.a₁) y h : E.toAffine.Point) = 0 := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some]
    simp only [Point.some.injEq]
    exact ⟨trivial, hneg.symm⟩
  exact Point.some_ne_zero h (hss _ htwo)

p2m_export "WeierstrassCurve" "a₁_eq_zero_of_forall_two_nsmul_eq_zero"

private theorem _root_.WeierstrassCurve.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero [IsAlgClosed F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0) :
    ∃ c : F, c ≠ 0 ∧ E.ΨSq n = C c := by
  have hroot : ∀ x : F, (E.ΨSq n).eval x ≠ 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
    have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy
    have hψ : (E.ψ n).evalEval x y = 0 := by
      have h2 := Affine.evalEval_psi_sq E hy n
      rw [hx] at h2
      exact pow_eq_zero_iff two_ne_zero |>.mp h2
    exact Point.some_ne_zero h (hss _ ((Point.smul_some_eq_zero_iff E h n).mpr hψ))
  have hne : E.ΨSq n ≠ 0 := fun h0 => hroot 0 (by rw [h0, eval_zero])
  have hdeg : (E.ΨSq n).degree = 0 := by
    by_contra hd
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
    exact hroot x hx
  refine ⟨(E.ΨSq n).coeff 0, ?_, eq_C_of_degree_le_zero (le_of_eq hdeg)⟩
  intro h0
  exact hne ((eq_C_of_degree_le_zero (le_of_eq hdeg)).trans (by rw [h0, C_0]))

p2m_export "WeierstrassCurve" "exists_PsiSq_eq_C_of_forall_zsmul_eq_zero"

private lemma _root_.WeierstrassCurve.fst_eq_of_zsmul_eq [DecidableEq F] (E : WeierstrassCurve F) {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0)
    {x₁ y₁ x₂ y₂ : F} {h₁ : E.toAffine.Nonsingular x₁ y₁} {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (he : n • Point.some x₁ y₁ h₁ = n • Point.some x₂ y₂ h₂) : x₁ = x₂ := by
  have h0 : n • (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) = 0 := by
    rw [zsmul_sub, he, sub_self]
  have hP := sub_eq_zero.mp (hss _ h0)
  exact (Point.some.inj hP).left

p2m_export "WeierstrassCurve" "fst_eq_of_zsmul_eq"

private theorem _root_.WeierstrassCurve.card_roots_toFinset_Phi_sub_C_le_two [IsAlgClosed F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0)
    {c : F} (hc : c ≠ 0) (hΨ : E.ΨSq n = C c) (w : F) :
    (E.Φ n - C w).roots.toFinset.card ≤ 2 := by

  have key : ∀ x ∈ (E.Φ n - C w).roots.toFinset, ∃ (y : F) (h : E.toAffine.Nonsingular x y)
      (y' : F) (h' : E.toAffine.Nonsingular (w / c) y'),
      n • Point.some x y h = Point.some (w / c) y' h' := by
    intro x hx
    have hΦ0 : E.Φ n - C w ≠ 0 := by
      intro h0
      have h1 := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_Φ, natDegree_zero] at h1
      exact pow_ne_zero 2 (by
        intro hn; rw [Int.natAbs_eq_zero] at hn; subst hn
        rw [ΨSq_zero] at hΨ; exact hc (C_eq_zero.mp hΨ.symm)) h1
    rw [Multiset.mem_toFinset, mem_roots hΦ0, IsRoot.def, eval_sub, eval_C, sub_eq_zero] at hx
    obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
    have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy
    have hψ : (E.ψ n).evalEval x y ≠ 0 := by
      intro h0
      have h2 := Affine.evalEval_psi_sq E hy n
      rw [h0, hΨ, eval_C, zero_pow two_ne_zero] at h2
      exact hc h2.symm
    obtain ⟨y', h', hP⟩ := Point.zsmul_some_eq_some_div E h hψ
    have hxw : (E.Φ n).eval x / (E.ΨSq n).eval x = w / c := by rw [hx, hΨ, eval_C]
    revert h' hP
    rw [hxw]
    intro h' hP
    exact ⟨y, h, y', h', hP⟩

  by_contra hgt
  rw [not_le, Finset.two_lt_card] at hgt
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h₁₂, h₁₃, h₂₃⟩ := hgt
  obtain ⟨y₁, h₁, y₁', h₁', e₁⟩ := key x₁ hx₁
  obtain ⟨y₂, h₂, y₂', h₂', e₂⟩ := key x₂ hx₂
  obtain ⟨y₃, h₃, y₃', h₃', e₃⟩ := key x₃ hx₃
  have hcard : ({y₁', y₂', y₃'} : Finset F).card ≤ 2 :=
    E.card_le_two_of_forall_equation (w / c) _ (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      exacts [h₁'.left, h₂'.left, h₃'.left])
  have hcol : y₁' = y₂' ∨ y₁' = y₃' ∨ y₂' = y₃' := by
    by_contra hne
    push Not at hne
    obtain ⟨n₁₂, n₁₃, n₂₃⟩ := hne
    have h3 : ({y₁', y₂', y₃'} : Finset F).card = 3 :=
      Finset.card_eq_three.mpr ⟨y₁', y₂', y₃', n₁₂, n₁₃, n₂₃, rfl⟩
    omega
  rcases hcol with hy | hy | hy
  · subst hy
    exact h₁₂ (E.fst_eq_of_zsmul_eq hss (e₁.trans e₂.symm))
  · subst hy
    exact h₁₃ (E.fst_eq_of_zsmul_eq hss (e₁.trans e₃.symm))
  · subst hy
    exact h₂₃ (E.fst_eq_of_zsmul_eq hss (e₂.trans e₃.symm))

p2m_export "WeierstrassCurve" "card_roots_toFinset_Phi_sub_C_le_two"

private theorem _root_.WeierstrassCurve.exists_Phi_eq_X_pow_add_C_of_forall_zsmul_eq_zero [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] [CharP F q] (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    ∃ β : F, E.Φ q = X ^ (q ^ 2) + C β := by
  rcases eq_or_ne q 2 with rfl | hq2
  ·
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hss2 : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0 := by
      intro P hP
      refine hss P ?_
      rw [Nat.cast_ofNat]
      exact_mod_cast hP
    have ha₁ : E.a₁ = 0 := E.a₁_eq_zero_of_forall_two_nsmul_eq_zero hss2
    have hb₄ : E.b₄ = 0 := by rw [b₄, ha₁]; linear_combination E.a₄ * h2
    have hb₆ : 2 * E.b₆ = 0 := by rw [h2, zero_mul]
    refine ⟨-E.b₈, ?_⟩
    rw [Nat.cast_ofNat, Φ_two, hb₄, hb₆, C_0, zero_mul, zero_mul, sub_zero, sub_zero, map_neg,
      ← sub_eq_add_neg]
    norm_num
  · obtain ⟨c, hc, hΨ⟩ := E.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero hss
    have hq3 : 3 ≤ q := by
      have h2 := hq.out.two_le
      omega
    have hmon : (E.Φ q).Monic := E.leadingCoeff_Φ q
    have hdeg : (E.Φ q).natDegree = q ^ 2 := by rw [natDegree_Φ, Int.natAbs_natCast]
    exact eq_X_pow_sq_add_C_of_card_roots_sub_C_le_two q hq3 hmon hdeg
      (E.card_roots_toFinset_Phi_sub_C_le_two hss hc hΨ)

p2m_export "WeierstrassCurve" "exists_Phi_eq_X_pow_add_C_of_forall_zsmul_eq_zero"
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine ΨSq_zero Affine.negY variableChange_j a₃ b_relation a₁ natDegree_Φ map j_of_char_two b₂ variableChange_b₂ twoTorsionPolynomial coe_Δ' map_j Φ_two Ψ₂Sq a₄ a₂ a₆ twoTorsionPolynomial_discr_ne_zero_of_isElliptic variableChange_b₆ map_id ΨSq toAffine Affine.Point Ψ₂Sq_eq b₆ b₈ variableChange_b₄ Δ c₄ VariableChange leadingCoeff_Φ map_Ψ₂Sq j b₄ Δ' Affine.evalEval_psi_sq Psi2Sq_ne_zero_of_isElliptic"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F]

noncomputable def deuringChange (u₀ r : F) (hu : u₀ ≠ 0) : VariableChange F :=
  ⟨(Units.mk0 u₀ hu)⁻¹, r, 0, 0⟩

lemma deuringChange_Psi2Sq_eval (E : WeierstrassCurve F) (u₀ r : F) (hu : u₀ ≠ 0)
    {x : F} (hx : E.Ψ₂Sq.eval x = 0) :
    ((deuringChange u₀ r hu • E).Ψ₂Sq).eval (u₀ ^ 2 * (x - r)) = 0 := by
  have hx' : 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 := by
    simpa [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X] using hx
  have hu1 : (deuringChange u₀ r hu).u⁻¹ = Units.mk0 u₀ hu := inv_inv _
  have huv : (((deuringChange u₀ r hu).u⁻¹ : Fˣ) : F) = u₀ := by rw [hu1]; rfl
  have hrv : (deuringChange u₀ r hu).r = r := rfl
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, huv, hrv]
  linear_combination (u₀ ^ 6) * hx'

lemma pow_q_sq_eq_of_Psi2Sq_eval_eq_zero [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (E : WeierstrassCurve F) [E.IsElliptic]
    {c : F} (hc : c ≠ 0) (hΨ : E.ΨSq (q : ℤ) = C c)
    {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β)
    {x : F} (hx : E.Ψ₂Sq.eval x = 0) :
    x ^ q ^ 2 = c * x - β := by
  have hodd : Odd q := hq.out.odd_of_ne_two hq2
  obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
  have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy

  have h2T : 2 • (Point.some x y h : E.toAffine.Point) = 0 :=
    (Point.two_smul_some_eq_zero_iff E h).mpr hx
  have hqT : q • (Point.some x y h : E.toAffine.Point) = Point.some x y h := by
    obtain ⟨k, hk⟩ := hodd
    have hq' : q = 2 * k + 1 := by omega
    rw [hq', add_nsmul, one_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add]

  have hsq : (E.ψ (q : ℤ)).evalEval x y ^ 2 = (E.ΨSq (q : ℤ)).eval x :=
    Affine.evalEval_psi_sq E hy (q : ℤ)
  rw [hΨ, eval_C] at hsq
  have hψ : (E.ψ (q : ℤ)).evalEval x y ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact hc hsq.symm

  obtain ⟨y', h', hdiv⟩ := Point.zsmul_some_eq_some_div E h hψ
  rw [natCast_zsmul, hqT] at hdiv
  simp only [Point.some.injEq] at hdiv
  have hxx := hdiv.1
  rw [hΨ, eval_C, eq_div_iff hc] at hxx
  have hΦx : (E.Φ (q : ℤ)).eval x = x ^ q ^ 2 + β := by
    rw [hΦ]
    simp [eval_add, eval_pow, eval_X, eval_C]
  linear_combination -hxx - hΦx

private theorem _root_.WeierstrassCurve.j_pow_q_sq_eq_j_of_Phi_eq_of_PsiSq_eq_C [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] [CharP F q] (hq2 : q ≠ 2)
    (E : WeierstrassCurve F) [E.IsElliptic] {c : F} (hc : c ≠ 0)
    (hΨ : E.ΨSq (q : ℤ) = C c) {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β) :
    E.j ^ q ^ 2 = E.j := by

  have h2 : (2 : F) ≠ 0 := by
    intro h20
    have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h20
    have := (CharP.cast_eq_zero_iff F q 2).mp h2'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
  have h4 : (4 : F) ≠ 0 := by
    have h42 : (4 : F) = 2 * 2 := by norm_num
    rw [h42]
    exact mul_ne_zero h2 h2

  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) two_pos
  have hu₀ne : u₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hu₀
    exact hc hu₀.symm

  have hP0 : E.twoTorsionPolynomial.toPoly ≠ 0 := by
    rw [← Ψ₂Sq_eq]
    exact Psi2Sq_ne_zero_of_isElliptic E
  have ha4 : E.twoTorsionPolynomial.a ≠ 0 := by
    simpa [twoTorsionPolynomial] using h4
  have hsplits : Splits (E.twoTorsionPolynomial.toPoly.map (RingHom.id F)) := by
    rw [Polynomial.map_id]
    exact IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha4).mp hsplits
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr h2)
  have hne := (Cubic.discr_ne_zero_iff_roots_ne ha4 h3).mp hdisc

  have hroots : ∀ z : F, z ∈ (Cubic.map (RingHom.id F) E.twoTorsionPolynomial).roots →
      E.Ψ₂Sq.eval z = 0 := by
    intro z hz
    rw [Cubic.map_roots, Polynomial.map_id, Polynomial.mem_roots hP0] at hz
    rw [Ψ₂Sq_eq]
    exact hz
  have hx₁ : E.Ψ₂Sq.eval x₁ = 0 := hroots x₁ (by rw [h3]; simp)
  have hx₂ : E.Ψ₂Sq.eval x₂ = 0 := hroots x₂ (by rw [h3]; simp)
  have hx₃ : E.Ψ₂Sq.eval x₃ = 0 := hroots x₃ (by rw [h3]; simp)

  set φ₂ : F →+* F := (frobenius F q).comp (frobenius F q) with hφ₂def
  set W₁ : WeierstrassCurve F := deuringChange u₀ (β / c) hu₀ne • E with hW₁
  set W₂ : WeierstrassCurve F := E.map φ₂ with hW₂
  have hφ₂pow : ∀ z : F, φ₂ z = z ^ q ^ 2 := by
    intro z
    have hzq : z ^ q ^ 2 = (z ^ q) ^ q := by rw [← pow_mul, pow_two]
    rw [hφ₂def, RingHom.comp_apply, frobenius_def, frobenius_def, hzq]

  have hpt : ∀ z : F, c * z - β = u₀ ^ 2 * (z - β / c) := by
    intro z
    rw [hu₀]
    field_simp

  have hvan : ∀ z : F, E.Ψ₂Sq.eval z = 0 →
      (W₁.Ψ₂Sq - W₂.Ψ₂Sq).eval (c * z - β) = 0 := by
    intro z hz
    rw [eval_sub]
    have hv₁ : W₁.Ψ₂Sq.eval (c * z - β) = 0 := by
      rw [hpt z, hW₁]
      exact deuringChange_Psi2Sq_eval E u₀ (β / c) hu₀ne hz
    have hzq : z ^ q ^ 2 = c * z - β :=
      pow_q_sq_eq_of_Psi2Sq_eval_eq_zero q hq2 E hc hΨ hΦ hz
    have hv₂ : W₂.Ψ₂Sq.eval (c * z - β) = 0 := by
      rw [hW₂, map_Ψ₂Sq, ← hzq, ← hφ₂pow z, eval_map_apply, hz, _root_.map_zero]
    rw [hv₁, hv₂, sub_zero]

  have himg : ∀ a b : F, c * a - β = c * b - β → a = b := by
    intro a b hab
    have hab' : c * a = c * b := by linear_combination hab
    exact mul_left_cancel₀ hc hab'
  have hv12 : c * x₁ - β ≠ c * x₂ - β := fun hcon => hne.1 (himg _ _ hcon)
  have hv13 : c * x₁ - β ≠ c * x₃ - β := fun hcon => hne.2.1 (himg _ _ hcon)
  have hv23 : c * x₂ - β ≠ c * x₃ - β := fun hcon => hne.2.2 (himg _ _ hcon)

  have hD : W₁.Ψ₂Sq - W₂.Ψ₂Sq = C (W₁.b₂ - W₂.b₂) * X ^ 2 +
      C (2 * W₁.b₄ - 2 * W₂.b₄) * X + C (W₁.b₆ - W₂.b₆) := by
    simp only [Ψ₂Sq, C_sub]
    ring
  have hcard3 : ({c * x₁ - β, c * x₂ - β, c * x₃ - β} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hv12, hv13]),
      Finset.card_insert_of_notMem (by simp [hv23]), Finset.card_singleton]
  have hzero : W₁.Ψ₂Sq - W₂.Ψ₂Sq = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (W₁.Ψ₂Sq - W₂.Ψ₂Sq) ({c * x₁ - β, c * x₂ - β, c * x₃ - β} : Finset F)
    · intro i hi
      rcases Finset.mem_insert.mp hi with h1 | hi'
      · rw [h1]; exact hvan x₁ hx₁
      rcases Finset.mem_insert.mp hi' with h2' | hi''
      · rw [h2']; exact hvan x₂ hx₂
      · rw [Finset.mem_singleton.mp hi'']; exact hvan x₃ hx₃
    · rw [hcard3, hD]
      exact lt_of_le_of_lt natDegree_quadratic_le (by norm_num)

  have hΨeq : W₁.Ψ₂Sq = W₂.Ψ₂Sq := sub_eq_zero.mp hzero
  have hcub : W₁.twoTorsionPolynomial = W₂.twoTorsionPolynomial := by
    rw [← Cubic.toPoly_injective, ← Ψ₂Sq_eq, ← Ψ₂Sq_eq]
    exact hΨeq
  have hb₂ : W₁.b₂ = W₂.b₂ := by
    have hcb := congrArg Cubic.b hcub
    simpa [twoTorsionPolynomial] using hcb
  have hb₄ : W₁.b₄ = W₂.b₄ := by
    have h24 : 2 * W₁.b₄ = 2 * W₂.b₄ := by
      have hcc := congrArg Cubic.c hcub
      simpa [twoTorsionPolynomial] using hcc
    exact mul_left_cancel₀ h2 h24
  have hb₆ : W₁.b₆ = W₂.b₆ := by
    have hcd := congrArg Cubic.d hcub
    simpa [twoTorsionPolynomial] using hcd
  have hb₈ : W₁.b₈ = W₂.b₈ := by
    have h48 : 4 * W₁.b₈ = 4 * W₂.b₈ := by
      rw [b_relation, b_relation, hb₂, hb₄, hb₆]
    exact mul_left_cancel₀ h4 h48

  have hc₄ : W₁.c₄ = W₂.c₄ := by
    rw [c₄, c₄, hb₂, hb₄]
  have hΔeq : W₁.Δ = W₂.Δ := by
    rw [Δ, Δ, hb₂, hb₄, hb₆, hb₈]
  have hΔ' : W₁.Δ' = W₂.Δ' := Units.ext (by rw [coe_Δ', coe_Δ', hΔeq])
  have hj : W₁.j = W₂.j := by
    rw [j, j, hΔ', hc₄]

  have hfrob : W₂.j = E.j ^ q ^ 2 := by
    have hmj : (E.map φ₂).j = φ₂ E.j := map_j E φ₂
    rw [hφ₂pow E.j] at hmj
    exact hmj
  calc E.j ^ q ^ 2 = W₂.j := hfrob.symm
    _ = W₁.j := hj.symm
    _ = E.j := variableChange_j _ _

p2m_export "WeierstrassCurve" "j_pow_q_sq_eq_j_of_Phi_eq_of_PsiSq_eq_C"
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine ΨSq_zero Affine.negY variableChange_j a₃ b_relation a₁ natDegree_Φ map j_of_char_two b₂ variableChange_b₂ twoTorsionPolynomial coe_Δ' map_j Φ_two Ψ₂Sq a₄ a₂ a₆ twoTorsionPolynomial_discr_ne_zero_of_isElliptic variableChange_b₆ map_id ΨSq toAffine Affine.Point Ψ₂Sq_eq b₆ b₈ variableChange_b₄ Δ c₄ VariableChange leadingCoeff_Φ map_Ψ₂Sq j b₄ Δ' Affine.evalEval_psi_sq Psi2Sq_ne_zero_of_isElliptic"
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F]

private theorem _root_.WeierstrassCurve.j_eq_zero_of_forall_two_nsmul_eq_zero [IsAlgClosed F] [DecidableEq F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0) : E.j = 0 := by
  rw [j_of_char_two, E.a₁_eq_zero_of_forall_two_nsmul_eq_zero hss]
  simp

p2m_export "WeierstrassCurve" "j_eq_zero_of_forall_two_nsmul_eq_zero"
end WeierstrassCurve

theorem solution
    {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] (q : ℕ) [Fact q.Prime]
    [CharP F q] (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    E.j ^ (q ^ 2) = E.j := by
  rcases eq_or_ne q 2 with rfl | hq2
  · have hss2 : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0 := by
      intro P hP
      refine hss P ?_
      rw [Nat.cast_ofNat]
      exact_mod_cast hP
    rw [E.j_eq_zero_of_forall_two_nsmul_eq_zero hss2]
    norm_num
  · obtain ⟨c, hc, hΨ⟩ := E.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero hss
    obtain ⟨β, hΦ⟩ := E.exists_Phi_eq_X_pow_add_C_of_forall_zsmul_eq_zero q hss
    exact E.j_pow_q_sq_eq_j_of_Phi_eq_of_PsiSq_eq_C q hq2 hc hΨ hΦ

end S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero (solution)
