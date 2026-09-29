-- Prove2me | solution 1 for WeierstrassCurve.exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b66c4d7b-4da4-52ab-9122-233eb34ba53c

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_RatPointHom
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace SupersingularMulP

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

omit [DecidableEq k] in
theorem exists_nonsingular (W : WeierstrassCurve k) [W.IsElliptic] (x : k) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set q : k[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    with hq
  have hdeg : q.degree = 2 := by
    rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; decide)
  refine ⟨y, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  simp only [hq, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy
  linear_combination hy

omit [IsAlgClosed k] [DecidableEq k] in
theorem exists_eq_some' {W : WeierstrassCurve k} {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀) (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable abbrev frobTwist (W : WeierstrassCurve k) : WeierstrassCurve k := W.map (frobenius k p)

scoped instance instIsEllipticFrobTwist (W : WeierstrassCurve k) [W.IsElliptic] : (frobTwist p W).IsElliptic := by
  unfold frobTwist; infer_instance

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve k) [W.IsElliptic] : (W.baseChange k).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular_iff (W : WeierstrassCurve k) (x y : k) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) ↔ W.toAffine.Nonsingular x y := by
  have := Affine.map_nonsingular W.toAffine (f := frobenius k p) (frobenius_inj k p) x y
  simpa only [frobenius_def] using this

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) :=
  (frob_nonsingular_iff p W x y).mpr h

noncomputable def frobPt (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (frobTwist p W).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (x ^ p) (y ^ p) (frob_nonsingular p W h)
  map_zero' := rfl
  map_add' := by
    have hf : ∀ z : k, frobenius k p z = z ^ p := frobenius_def p
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
      have h2 : y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p) := by
        rw [hxy.right, ← hf, ← hf, ← hf, Affine.map_negY]
      rw [Affine.Point.add_of_Y_eq (congr_arg (· ^ p) hxy.left) h2]
    · have hxy' : ¬ (x₁ ^ p = x₂ ^ p ∧
          y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
        rintro ⟨e1, e2⟩
        apply hxy
        refine ⟨frobenius_inj k p (by rw [hf, hf]; exact e1), frobenius_inj k p ?_⟩
        rw [hf, hf, e2, ← hf, ← hf, Affine.map_negY, hf]
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      simp only [Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addX]
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addY]

theorem frobPt_some (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    frobPt p W (.some x y h) = .some (x ^ p) (y ^ p) (frob_nonsingular p W h) := rfl

theorem frobPt_injective (W : WeierstrassCurve k) : Function.Injective (frobPt p W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [frobPt_some, frobPt_some, Affine.Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have hx : x₁ = x₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e1)
    have hy : y₁ = y₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e2)
    subst hx hy
    rfl

theorem frobPt_surjective (W : WeierstrassCurve k) : Function.Surjective (frobPt p W) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rintro (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq u hp
    obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq v hp
    exact ⟨.some x y ((frob_nonsingular_iff p W x y).mp h), rfl⟩

theorem frobPt_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] : frobPt p W ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W 0
  intro h0
  have : frobPt p W (.some 0 y hy) = 0 := by rw [h0]; rfl
  rw [frobPt_some] at this
  exact Affine.Point.some_ne_zero _ this

theorem frobPt_mem_rationalHomSet (W : WeierstrassCurve k) :
    (frobPt p W : (W.baseChange k).toAffine.Point →+ ((frobTwist p W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (frobTwist p W) := by
  refine Or.inr ⟨C (X ^ p), 1, X ^ p, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : k[X][X]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C (X ^ p) : k[X][X]) x y = x ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (X ^ p : k[X][X]) x y = y ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  simp only [e0, e1, e2, div_one]
  exact ⟨frob_nonsingular p W h, rfl⟩

theorem frobPt_frobPt_some (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (frobPt p (frobTwist p W)) (frobPt p W (.some x y h)) =
      .some (x ^ p ^ 2) (y ^ p ^ 2) (by
        have h1 := frob_nonsingular p (frobTwist p W) (frob_nonsingular p W h)
        rwa [← pow_mul, ← pow_mul, ← sq] at h1) := by
  rw [frobPt_some, frobPt_some]
  congr 1 <;> rw [← pow_mul, ← sq]

theorem nsmul_id_mem_rationalHomSet (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    ((n : ℕ) • AddMonoidHom.id W.toAffine.Point : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W := by
  induction n with
  | zero => rw [zero_nsmul]; exact WeierstrassCurve.zero_mem_rationalHomSet k W W
  | succ n ih =>
    rw [succ_nsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W W ih (WeierstrassCurve.id_mem_rationalHomSet k W)

end Frobenius

section MulP

variable (p : ℕ) [Fact p.Prime] [CharP k p]

omit [CharP k p] in

theorem Phi_PsiSq_of_supersingular (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ b d : k, d ≠ 0 ∧ X.ΨSq p = C d ∧ X.Φ p = Polynomial.X ^ p ^ 2 + C b ∧
      ∀ (x y : k) (h : X.toAffine.Nonsingular x y),
        ∃ y' h', p • (WeierstrassCurve.Affine.Point.some x y h : X.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some ((X.Φ p).eval x / d) y' h' := by

  have hψ : ∀ (x y : k) (h : X.toAffine.Nonsingular x y), (X.ψ p).evalEval x y ≠ 0 := by
    intro x y h h0
    have h1 : ((p : ℤ)) • (WeierstrassCurve.Affine.Point.some x y h) = 0 :=
      (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff X h (p : ℤ)).mpr h0
    rw [natCast_zsmul] at h1
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ (hss _ h1)

  have hΨroot : ∀ x : k, (X.ΨSq p).eval x ≠ 0 := by
    intro x
    obtain ⟨y, h⟩ := exists_nonsingular X x
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq X h.left (p : ℤ)]
    exact pow_ne_zero 2 (hψ x y h)
  have hΨdeg : (X.ΨSq p).degree = 0 := by
    by_contra hd
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X.ΨSq p) hd
    exact hΨroot x hx
  set d := (X.ΨSq p).coeff 0 with hddef
  have hΨC : X.ΨSq p = C d := eq_C_of_degree_eq_zero hΨdeg
  have hd0 : d ≠ 0 := by
    intro h0
    apply hΨroot 0
    rw [hΨC, h0, map_zero, eval_zero]

  have hmul : ∀ (x y : k) (h : X.toAffine.Nonsingular x y),
      ∃ y' h', p • (WeierstrassCurve.Affine.Point.some x y h : X.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some ((X.Φ p).eval x / d) y' h' := by
    intro x y h
    obtain ⟨y', h', hP⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div X h (n := p) (hψ x y h)
    have hev : (X.ΨSq p).eval x = d := by rw [hΨC, eval_C]
    rw [natCast_zsmul] at hP
    exact ⟨y', exists_eq_some' hP (by rw [hev]) rfl⟩

  have hinj : ∀ x₁ x₂ : k, (X.Φ p).eval x₁ = (X.Φ p).eval x₂ → x₁ = x₂ := by
    intro x₁ x₂ hΦ
    obtain ⟨y₁, h₁⟩ := exists_nonsingular X x₁
    obtain ⟨y₂, h₂⟩ := exists_nonsingular X x₂
    obtain ⟨y₁', h₁', hP₁⟩ := hmul x₁ y₁ h₁
    obtain ⟨y₂', h₂', hP₂⟩ := hmul x₂ y₂ h₂
    have hxx : (X.Φ p).eval x₁ / d = (X.Φ p).eval x₂ / d := by rw [hΦ]
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁'.left h₂'.left hxx with hy | hy
    · have heq : p • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) =
          p • WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
        rw [hP₁, hP₂]
        exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _ |>.mpr ⟨hxx, hy⟩
      have h0 : p • ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) -
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 := by rw [smul_sub, heq, sub_self]
      have := sub_eq_zero.mp (hss _ h0)
      exact (WeierstrassCurve.Affine.Point.some.inj this).left
    · have heq : p • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) =
          -(p • WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
        rw [hP₁, hP₂, WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _ |>.mpr ⟨hxx, hy⟩
      have h0 : p • ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 := by rw [smul_add, heq, neg_add_cancel]
      have := eq_neg_of_add_eq_zero_left (hss _ h0)
      rw [WeierstrassCurve.Affine.Point.neg_some] at this
      exact (WeierstrassCurve.Affine.Point.some.inj this).left

  set b := (X.Φ p).eval 0 with hbdef
  set F := X.Φ p - C b with hF
  have hFdeg : F.natDegree = p ^ 2 := by
    have := WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq X p (b * d⁻¹)
    rwa [hΨC, ← C_mul, inv_mul_cancel_right₀ hd0, Int.natAbs_natCast] at this
  have hΦdeg : 0 < (X.Φ p).degree := by
    rw [degree_eq_natDegree (WeierstrassCurve.Φ_ne_zero (W := X) p), WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos 2
  have hFmonic : F.Monic := by
    rw [Monic, hF, leadingCoeff_sub_of_degree_lt (lt_of_le_of_lt degree_C_le hΦdeg), WeierstrassCurve.leadingCoeff_Φ]
  have hFroots : F.roots = Multiset.replicate (p ^ 2) 0 := by
    rw [Multiset.eq_replicate]
    refine ⟨by rw [IsAlgClosed.card_roots_eq_natDegree, hFdeg], fun x hx => ?_⟩
    have hx' : F.IsRoot x := (mem_roots hFmonic.ne_zero).mp hx
    rw [IsRoot.def, hF, eval_sub, eval_C, sub_eq_zero] at hx'
    exact hinj x 0 hx'
  have hFeq : F = Polynomial.X ^ p ^ 2 := by
    have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFmonic
      (by rw [IsAlgClosed.card_roots_eq_natDegree])
    rw [hFroots, Multiset.map_replicate, Multiset.prod_replicate, map_zero, sub_zero] at this
    exact this.symm
  refine ⟨b, d, hd0, hΨC, ?_, hmul⟩
  rw [← sub_eq_iff_eq_add, ← hF, hFeq]

end MulP

section Main

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem main (W : WeierstrassCurve k) [W.IsElliptic] (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (ε : (frobTwist p (frobTwist p W)).toAffine.Point →+ W.toAffine.Point)
      (ε' : W.toAffine.Point →+ (frobTwist p (frobTwist p W)).toAffine.Point),
      ε ∈ rationalHomSet k (frobTwist p (frobTwist p W)) W ∧
      ε' ∈ rationalHomSet k W (frobTwist p (frobTwist p W)) ∧
      ε.comp ε' = AddMonoidHom.id _ ∧ ε'.comp ε = AddMonoidHom.id _ ∧
      (p : ℕ) • AddMonoidHom.id W.toAffine.Point = ε.comp ((frobPt p (frobTwist p W)).comp (frobPt p W)) ∧
      (frobPt p (frobTwist p W)).comp (frobPt p W) = ε'.comp ((p : ℕ) • AddMonoidHom.id W.toAffine.Point) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨b, d, hd0, hΨ, hΦ, hmul⟩ := Phi_PsiSq_of_supersingular p W hss

  set FF : W.toAffine.Point →+ (frobTwist p (frobTwist p W)).toAffine.Point :=
    (frobPt p (frobTwist p W)).comp (frobPt p W) with hFF
  set MP : W.toAffine.Point →+ W.toAffine.Point := (p : ℕ) • AddMonoidHom.id W.toAffine.Point with hMP
  have hMP_apply : ∀ P, MP P = p • P := fun P => rfl
  have hFFmem : FF ∈ rationalHomSet k W (frobTwist p (frobTwist p W)) :=
    WeierstrassCurve.comp_mem_rationalHomSet k W (frobTwist p W) (frobTwist p (frobTwist p W))
      (frobPt_mem_rationalHomSet p W) (frobPt_mem_rationalHomSet p (frobTwist p W))
  have hMPmem : MP ∈ rationalHomSet k W W := nsmul_id_mem_rationalHomSet W p
  have hFFinj : Function.Injective FF := (frobPt_injective p (frobTwist p W)).comp (frobPt_injective p W)
  have hFFsurj : Function.Surjective FF := (frobPt_surjective p (frobTwist p W)).comp (frobPt_surjective p W)
  have hMPinj : Function.Injective MP := by
    intro P Q hPQ
    rw [hMP_apply, hMP_apply] at hPQ
    have h0 : p • (P - Q) = 0 := by rw [smul_sub, hPQ, sub_self]
    exact sub_eq_zero.mp (hss _ h0)
  obtain ⟨y0, hy0⟩ := exists_nonsingular W 0
  have hFF0 : FF ≠ 0 := by
    intro h0
    have h1 : FF (.some 0 y0 hy0) = FF 0 := by rw [h0]; rfl
    exact Affine.Point.some_ne_zero _ (hFFinj h1)
  have hMP0 : MP ≠ 0 := by
    intro h0
    have h1 : MP (.some 0 y0 hy0) = MP 0 := by rw [h0]; rfl
    exact Affine.Point.some_ne_zero _ (hMPinj h1)
  have hMPsurj : Function.Surjective MP := WeierstrassCurve.surjective_of_mem_rationalHomSet k hMPmem hMP0

  have hX1 : IsCoprime (X : k[X]) 1 := isCoprime_one_right
  have hX1w : wronskian (X : k[X]) 1 ≠ 0 := by simp [wronskian]
  have hLd : IsCoprime (X + C b : k[X]) (C d) :=
    ⟨0, C d⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hd0, C_1]⟩
  have hLdw : wronskian (X + C b : k[X]) (C d) ≠ 0 := by
    have : wronskian (X + C b : k[X]) (C d) = -C d := by
      simp only [wronskian, derivative_C, mul_zero, derivative_add, derivative_X, add_zero, one_mul, zero_sub]
    rw [this, neg_ne_zero, Ne, ← map_zero C, C_inj]
    exact hd0

  have hFFx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ (∅ : Set k) →
      ∃ (x' y' : k) (h' : (frobTwist p (frobTwist p W)).toAffine.Nonsingular x' y'),
        FF (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * (1 : k[X]).eval (x ^ p ^ 2) = (X : k[X]).eval (x ^ p ^ 2) := by
    intro x y h _
    exact ⟨x ^ p ^ 2, y ^ p ^ 2, _, by rw [hFF, AddMonoidHom.comp_apply, frobPt_frobPt_some], by simp⟩
  have hMPx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ (∅ : Set k) →
      ∃ (x' y' : k) (h' : W.toAffine.Nonsingular x' y'),
        MP (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * (C d : k[X]).eval (x ^ p ^ 2) = (X + C b : k[X]).eval (x ^ p ^ 2) := by
    intro x y h _
    obtain ⟨y', h', hP⟩ := hmul x y h
    refine ⟨(W.Φ p).eval x / d, y', h', by rw [hMP_apply]; exact hP, ?_⟩
    rw [eval_C, div_mul_cancel₀ _ hd0, hΦ, eval_add, eval_add, eval_pow, eval_X, eval_C, eval_X, eval_C]
  have hker1 : ∀ T : W.toAffine.Point, FF T = 0 → MP T = 0 := fun T hT => by
    have hT0 : T = 0 := hFFinj (by rw [hT, map_zero])
    rw [hT0, map_zero]
  have hker2 : ∀ T : W.toAffine.Point, MP T = 0 → FF T = 0 := fun T hT => by
    have hT0 : T = 0 := hMPinj (by rw [hT, map_zero])
    rw [hT0, map_zero]
  obtain ⟨ε, hε, hMPε⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W
    (frobTwist p (frobTwist p W)) W hFFmem hMPmem hFF0 hMP0 hker1 2 hX1 hX1w hLd Set.finite_empty hFFx hMPx
  obtain ⟨ε', hε', hFFε'⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W
    W (frobTwist p (frobTwist p W)) hMPmem hFFmem hMP0 hFF0 hker2 2 hLd hLdw hX1 Set.finite_empty hMPx hFFx

  have h1 : ε.comp ε' = AddMonoidHom.id _ := by
    ext Q
    obtain ⟨P, rfl⟩ := hMPsurj Q
    calc (ε.comp ε') (MP P) = ε ((ε'.comp MP) P) := rfl
      _ = ε (FF P) := congrArg ε (DFunLike.congr_fun hFFε' P).symm
      _ = (ε.comp FF) P := rfl
      _ = MP P := (DFunLike.congr_fun hMPε P).symm
  have h2 : ε'.comp ε = AddMonoidHom.id _ := by
    ext Q
    obtain ⟨P, rfl⟩ := hFFsurj Q
    calc (ε'.comp ε) (FF P) = ε' ((ε.comp FF) P) := rfl
      _ = ε' (MP P) := congrArg ε' (DFunLike.congr_fun hMPε P).symm
      _ = (ε'.comp MP) P := rfl
      _ = FF P := (DFunLike.congr_fun hFFε' P).symm
  exact ⟨ε, ε', hε, hε', h1, h2, hMPε, hFFε'⟩

end Main

end SupersingularMulP
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero.SupersingularMulP"

theorem SupersingularMulP.frobPt_eq_ratPointHom {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (W : WeierstrassCurve κ) :
    SupersingularMulP.frobPt p W = WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W) := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic] (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (ε : ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point →+ W.toAffine.Point)
      (ε' : W.toAffine.Point →+ ((W.map (frobenius κ p)).map (frobenius κ p)).toAffine.Point),
      ε ∈ WeierstrassCurve.rationalHomSet κ ((W.map (frobenius κ p)).map (frobenius κ p)) W ∧
      ε' ∈ WeierstrassCurve.rationalHomSet κ W ((W.map (frobenius κ p)).map (frobenius κ p)) ∧
      ε.comp ε' = AddMonoidHom.id _ ∧ ε'.comp ε = AddMonoidHom.id _ ∧
      (p : ℕ) • AddMonoidHom.id W.toAffine.Point =
        ε.comp ((WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W))) ∧
      (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W.map (frobenius κ p))).comp
          (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) =
        ε'.comp ((p : ℕ) • AddMonoidHom.id W.toAffine.Point) := by
  rw [← SupersingularMulP.frobPt_eq_ratPointHom, ← SupersingularMulP.frobPt_eq_ratPointHom]
  exact SupersingularMulP.main p W hss

end S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero (solution)
