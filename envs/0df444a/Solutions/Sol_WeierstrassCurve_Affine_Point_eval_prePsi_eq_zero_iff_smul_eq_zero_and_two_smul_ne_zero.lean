-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/23b7083e-cc53-5d8d-9a85-22b426b13156

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

namespace P2M
namespace PrePsiRoots

section Semantics

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem evalEval_eq_of_mk_eq {x y : F} (hxy : W.toAffine.Equation x y) {a b : F[X][Y]}
    (hab : Affine.CoordinateRing.mk W a = Affine.CoordinateRing.mk W b) : a.evalEval x y = b.evalEval x y := by
  have h := congrArg (AdjoinRoot.evalEval hxy) hab
  rwa [Affine.CoordinateRing.mk, AdjoinRoot.evalEval_mk, AdjoinRoot.evalEval_mk] at h

theorem evalEval_ψ_natCast {x y : F} (hxy : W.toAffine.Equation x y) (n : ℕ) :
    (W.ψ n).evalEval x y = (W.preΨ' n).eval x * (if Even n then W.ψ₂.evalEval x y else 1) := by
  rw [evalEval_eq_of_mk_eq W hxy (Affine.CoordinateRing.mk_ψ (W := W) n), Ψ_ofNat, evalEval_mul, evalEval_C]
  split_ifs <;> simp [evalEval_one]

theorem evalEval_ψ₂_sq {x y : F} (hxy : W.toAffine.Equation x y) :
    (W.ψ₂.evalEval x y) ^ 2 = W.Ψ₂Sq.eval x := by
  have h := evalEval_eq_of_mk_eq W hxy (Affine.CoordinateRing.mk_ψ₂_sq (W := W))
  rwa [evalEval_pow, evalEval_C] at h

theorem nsmul_eq_zero_of_eval_preΨ' {x y : F} (hxy : W.toAffine.Nonsingular x y) {m : ℕ}
    (hm : (W.preΨ' m).eval x = 0) : m • Affine.Point.some x y hxy = 0 := by
  rw [← natCast_zsmul, Affine.Point.smul_some_eq_zero_iff W hxy, evalEval_ψ_natCast W hxy.left, hm, zero_mul]

theorem eval_preΨ'_eq_zero_of_nsmul_eq_zero {x y : F} (hxy : W.toAffine.Nonsingular x y) {m : ℕ}
    (hm : m • Affine.Point.some x y hxy = 0) (h2 : 2 • Affine.Point.some x y hxy ≠ 0) :
    (W.preΨ' m).eval x = 0 := by
  rw [← natCast_zsmul, Affine.Point.smul_some_eq_zero_iff W hxy, evalEval_ψ_natCast W hxy.left] at hm
  rcases mul_eq_zero.mp hm with h | h
  · exact h
  · split_ifs at h with he
    · exfalso
      apply h2
      rw [Affine.Point.two_smul_some_eq_zero_iff W hxy, ← evalEval_ψ₂_sq W hxy.left, h]
      ring
    · exact absurd h one_ne_zero

theorem exists_nonsingular [W.IsElliptic] [IsAlgClosed F] (x : F) : ∃ y : F, W.toAffine.Nonsingular x y := by
  set g : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) with hg
  have hdeg : g.degree = 2 := by
    rw [hg]
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root g (by rw [hdeg]; norm_num)
  refine ⟨y, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  rw [IsRoot, hg] at hy
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy
  linear_combination hy

end Semantics

section Count

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed F]

def T (n : ℕ) : Set E.toAffine.Point := {P | n • P = 0 ∧ 2 • P ≠ 0}

def X (n : ℕ) : Set F := {x | ∃ (y : F) (h : E.toAffine.Nonsingular x y), Affine.Point.some x y h ∈ T E n}

theorem neg_mem_T {n : ℕ} {P : E.toAffine.Point} (hP : P ∈ T E n) : -P ∈ T E n := by
  refine ⟨by rw [neg_nsmul, hP.1, neg_zero], fun h => hP.2 ?_⟩
  rw [neg_nsmul, neg_eq_zero] at h
  exact h

noncomputable def pt (x : F) : E.toAffine.Point :=
  Affine.Point.some x (Classical.choose (exists_nonsingular E x)) (Classical.choose_spec (exists_nonsingular E x))

theorem eq_pt_or_eq_neg {x y : F} (hxy : E.toAffine.Nonsingular x y) :
    Affine.Point.some x y hxy = pt E x ∨ Affine.Point.some x y hxy = -pt E x :=
  (Affine.Point.X_eq_iff (W := E.toAffine) (h₁ := hxy) (h₂ := Classical.choose_spec (exists_nonsingular E x))).mp rfl

theorem pt_mem_T {n : ℕ} {x : F} (hx : x ∈ X E n) : pt E x ∈ T E n := by
  obtain ⟨y, hxy, hP⟩ := hx
  rcases eq_pt_or_eq_neg E hxy with he | he
  · rwa [he] at hP
  · have := neg_mem_T E hP
    rwa [he, neg_neg] at this

theorem two_smul_pt_ne_zero {n : ℕ} {x : F} (hx : x ∈ X E n) : 2 • pt E x ≠ 0 := (pt_mem_T E hx).2

theorem T_eq_union (n : ℕ) : T E n = pt E '' X E n ∪ (fun x => -pt E x) '' X E n := by
  ext P
  constructor
  · intro hP
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd (by rw [← Affine.Point.zero_def, smul_zero]) hP.2
    · have hx : x ∈ X E n := ⟨y, hxy, hP⟩
      rcases eq_pt_or_eq_neg E hxy with he | he
      · exact Or.inl ⟨x, hx, he.symm⟩
      · exact Or.inr ⟨x, hx, he.symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact pt_mem_T E hx
    · exact neg_mem_T E (pt_mem_T E hx)

theorem pt_injective : Function.Injective (pt E) := by
  intro x x' h
  rw [pt, pt, Affine.Point.some.injEq] at h
  exact h.1

theorem negpt_injective : Function.Injective (fun x => -pt E x) := by
  intro x x' h
  exact pt_injective E (neg_injective h)

theorem disjoint_images (n : ℕ) : Disjoint (pt E '' X E n) ((fun x => -pt E x) '' X E n) := by
  rw [Set.disjoint_left]
  rintro P ⟨x, hx, rfl⟩ ⟨x', -, he⟩

  have hxx : x' = x := by
    have h1 : -pt E x' = pt E x := he
    rw [pt, Affine.Point.neg_some, pt, Affine.Point.some.injEq] at h1
    exact h1.1
  subst hxx
  apply two_smul_pt_ne_zero E hx
  rw [two_nsmul]
  have h1 : -pt E x' = pt E x' := he
  nth_rewrite 1 [← h1]
  exact neg_add_cancel _

theorem X_subset_roots {n : ℕ} (hn : (n : F) ≠ 0) : X E n ⊆ ↑(E.preΨ' n).roots.toFinset := by
  rintro x ⟨y, hxy, hT⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (E.preΨ'_ne_zero hn)]
  exact eval_preΨ'_eq_zero_of_nsmul_eq_zero E hxy hT.1 hT.2

theorem X_finite {n : ℕ} (hn : (n : F) ≠ 0) : (X E n).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (X_subset_roots E hn)

end Count

section BaseChange

variable {F₀ : Type u} {F : Type u} [Field F₀] [Field F] [Algebra F₀ F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F₀) [W.IsElliptic]

scoped instance isElliptic_baseChange : (W.baseChange F).IsElliptic := by
  show (W.map (algebraMap F₀ F)).IsElliptic
  infer_instance

theorem ncard_torsion {m : ℕ} (hm : (m : F) ≠ 0) :
    {P : (W.baseChange F).toAffine.Point | m • P = 0}.ncard = m ^ 2 := by
  obtain ⟨e⟩ := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := F) hm
  have hset : {P : (W.baseChange F).toAffine.Point | m • P = 0} =
      ↑(Submodule.torsionBy ℤ (W.baseChange F).toAffine.Point m) := by
    ext P
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff]
    rw [← natCast_zsmul]
  rw [hset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_congr e.symm.toEquiv, Nat.card_prod,
    Nat.card_zmod, sq]

theorem X_eq_roots {n : ℕ} (hn : (n : F) ≠ 0) :
    X (W.baseChange F) n = ↑((W.baseChange F).preΨ' n).roots.toFinset := by
  set E : WeierstrassCurve F := W.baseChange F with hE
  set c : ℕ := if Even n then 4 else 1 with hc

  have hD : (((E.preΨ' n).roots.toFinset : Finset F) : Set F).ncard ≤ (n ^ 2 - c) / 2 := by
    rw [Set.ncard_coe_finset, hc, ← E.natDegree_preΨ' hn]
    exact (Multiset.toFinset_card_le _).trans (card_roots' _)

  have hT : (T E n).ncard = 2 * (X E n).ncard := by
    rw [T_eq_union, Set.ncard_union_eq (disjoint_images E n) ((X_finite E hn).image _) ((X_finite E hn).image _),
      Set.ncard_image_of_injective _ (pt_injective E), Set.ncard_image_of_injective _ (negpt_injective E)]
    ring

  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have htors : {P : E.toAffine.Point | n • P = 0}.ncard = n ^ 2 := ncard_torsion W hn
  have hfin : {P : E.toAffine.Point | n • P = 0}.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [htors]; positivity)
  have hsub : {P : E.toAffine.Point | n • P = 0 ∧ 2 • P = 0} ⊆ {P | n • P = 0} := fun P hP => hP.1
  have hTeq : T E n = {P : E.toAffine.Point | n • P = 0} \ {P | n • P = 0 ∧ 2 • P = 0} := by
    ext P
    simp only [T, Set.mem_diff, Set.mem_setOf_eq]
    tauto
  have hC : {P : E.toAffine.Point | n • P = 0 ∧ 2 • P = 0}.ncard = c := by
    rw [hc]
    split_ifs with he
    ·
      obtain ⟨m, hm⟩ := he
      have h2 : (2 : F) ≠ 0 := by
        intro h0; apply hn
        rw [hm, Nat.cast_add, ← two_mul, h0, zero_mul]
      have hset : {P : E.toAffine.Point | n • P = 0 ∧ 2 • P = 0} = {P | 2 • P = 0} := by
        ext P
        simp only [Set.mem_setOf_eq]
        constructor
        · exact And.right
        · intro h2P
          refine ⟨?_, h2P⟩
          rw [hm, ← two_mul, mul_comm, mul_nsmul', h2P, smul_zero]
      rw [hset]
      have := ncard_torsion (F := F) W (m := 2) (by exact_mod_cast h2)
      simpa using this
    ·
      obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp he
      have hset : {P : E.toAffine.Point | n • P = 0 ∧ 2 • P = 0} = {0} := by
        ext P
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hnP, h2P⟩
          have : P = (2 * m + 1) • P - m • (2 • P) := by
            rw [add_nsmul, one_nsmul, mul_comm, mul_nsmul']
            abel
          rw [this, ← hm, hnP, h2P, smul_zero, sub_zero]
        · rintro rfl
          exact ⟨smul_zero _, smul_zero _⟩
      rw [hset, Set.ncard_singleton]
  have hTval : (T E n).ncard = n ^ 2 - c := by
    rw [hTeq, Set.ncard_diff hsub (hfin.subset hsub), htors, hC]

  apply Set.eq_of_subset_of_ncard_le (X_subset_roots E hn) ?_ (Finset.finite_toSet _)
  omega

theorem two_smul_ne_zero_of_eval_preΨ'_baseChange {n : ℕ} (hn : (n : F) ≠ 0) {x y : F}
    (hxy : (W.baseChange F).toAffine.Nonsingular x y) (hx : ((W.baseChange F).preΨ' n).eval x = 0) :
    2 • Affine.Point.some x y hxy ≠ 0 := by
  have hmem : x ∈ X (W.baseChange F) n := by
    rw [X_eq_roots W hn, Finset.mem_coe, Multiset.mem_toFinset, mem_roots ((W.baseChange F).preΨ'_ne_zero hn)]
    exact hx
  obtain ⟨y', hxy', hT⟩ := hmem
  intro h2
  apply hT.2
  rw [Affine.Point.two_smul_some_eq_zero_iff] at h2 ⊢
  exact h2

end BaseChange

end P2M.PrePsiRoots
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero.P2M P2MW.S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero.P2M.PrePsiRoots"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero.P2M"

open P2M.PrePsiRoots in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : F) ≠ 0) {x y : F} (h : W.toAffine.Nonsingular x y) :
    (W.preΨ' n).eval x = 0 ↔
      n • WeierstrassCurve.Affine.Point.some x y h = 0 ∧ 2 • WeierstrassCurve.Affine.Point.some x y h ≠ 0 := by
  classical
  constructor
  · intro hx
    refine ⟨nsmul_eq_zero_of_eval_preΨ' W h hx, ?_⟩

    let K : Type u := AlgebraicClosure F
    let ι : F →+* K := algebraMap F K
    have hι : Function.Injective ι := ι.injective
    have hnK : (n : K) ≠ 0 := by
      intro h0; apply hn
      apply hι
      rw [map_natCast, map_zero]; exact h0
    have hxy' : (W.baseChange K).toAffine.Nonsingular (ι x) (ι y) := by
      show (W.map ι).toAffine.Nonsingular (ι x) (ι y)
      exact (Affine.map_nonsingular (W := W.toAffine) hι x y).mpr h
    have hx' : ((W.baseChange K).preΨ' n).eval (ι x) = 0 := by
      show ((W.map ι).preΨ' n).eval (ι x) = 0
      rw [map_preΨ', eval_map, eval₂_at_apply, hx, map_zero]
    have h2K := two_smul_ne_zero_of_eval_preΨ'_baseChange (F := K) W hnK hxy' hx'
    intro h2
    apply h2K
    rw [Affine.Point.two_smul_some_eq_zero_iff] at h2 ⊢
    show (W.map ι).Ψ₂Sq.eval (ι x) = 0
    rw [map_Ψ₂Sq, eval_map, eval₂_at_apply, h2, map_zero]
  · rintro ⟨hnP, h2P⟩
    exact eval_preΨ'_eq_zero_of_nsmul_eq_zero W h hnP h2P

end S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero (solution)
