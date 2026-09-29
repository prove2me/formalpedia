-- Prove2me | solution 1 for WeierstrassCurve.dualIsogenyExistence_rationalEndSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fb24f73b-4942-5be6-96da-dee69a83c1eb

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_comp
import Theorems.Thm_WeierstrassCurve_Affine_Point_natDegree_parallelogram_law
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ natDegree_Φ map natDegree_ΨSq_le Affine.Point.some Affine.Point.some.injEq Affine.degree_polynomial ψ₂_sq ψ_two ΨSq toAffine Affine.Point Affine.nonsingular_neg Affine.monic_polynomial Affine.Point.some_ne_zero baseChange ΨSq_two evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet add_mem_rationalHomSet comp_mem_rationalHomSet exists_xCoord_rep_of_mem_rationalHomSet natDegree_lt_of_xCoord_rep exists_xCoord_rep_comp Affine.Point.natDegree_parallelogram_law Affine.Point.zsmul_some_eq_some_div isCoprime_Phi_PsiSq Psi2Sq_ne_zero_of_isElliptic"
namespace DualExist
p2m_open "WeierstrassCurve"

section Algebra

variable {R : Type*} [Ring R] (q : R → ℤ)
  (para : ∀ a b : R, q (a + b) + q (a - b) = 2 * q a + 2 * q b)
include para

theorem q_zero : q 0 = 0 := by
  have := para 0 0; rw [add_zero, sub_zero] at this; linarith

theorem q_neg (a : R) : q (-a) = q a := by
  have := para 0 a; rw [zero_add, zero_sub, q_zero q para] at this; linarith

omit para in

theorem eq_quadratic_of_second_diff (f : ℤ → ℤ) (c : ℤ)
    (h : ∀ m : ℤ, f (m + 1) + f (m - 1) = 2 * f m + 2 * c) (m : ℤ) :
    f m = f 0 + m * (f 1 - f 0 - c) + m ^ 2 * c := by
  suffices H : ∀ m : ℤ, f m = f 0 + m * (f 1 - f 0 - c) + m ^ 2 * c ∧
      f (m + 1) = f 0 + (m + 1) * (f 1 - f 0 - c) + (m + 1) ^ 2 * c from (H m).1
  intro m
  induction m using Int.induction_on with
  | zero => refine ⟨by simp, ?_⟩; simp only [zero_add, one_pow, one_mul]; ring
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hh := h ((i : ℤ) + 1)
    rw [show (i : ℤ) + 1 - 1 = i by ring] at hh
    linear_combination hh - h1 + 2 * h2
  | pred i ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, by rw [show (-(i : ℤ) - 1 + 1) = -i by ring]; exact h1⟩
    have hh := h (-(i : ℤ))
    linear_combination hh - h2 + 2 * h1

theorem q_line (a e : R) (m : ℤ) :
    q (a + (m : R) * e) = q a + m * (q (a + e) - q a - q e) + m ^ 2 * q e := by
  have key := eq_quadratic_of_second_diff (fun m : ℤ => q (a + (m : R) * e)) (q e) ?_ m
  · simpa using key
  · intro m
    have := para (a + (m : R) * e) e
    simp only [Int.cast_add, Int.cast_one, Int.cast_sub]
    rw [show a + ((m : R) + 1) * e = a + (m : R) * e + e by rw [add_mul, one_mul, add_assoc],
      show a + ((m : R) - 1) * e = a + (m : R) * e - e by rw [sub_mul, one_mul, add_sub_assoc]]
    exact this

variable (one : q 1 = 1) (mul : ∀ a b : R, q (a * b) = q a * q b)
include one mul

theorem q_charPoly (φ : R) (n t : ℤ) (hn : q φ = n) (ht : q (1 + φ) = 1 + t + n) :
    q (φ * φ - (t : R) * φ + (n : R)) = 0 := by

  have h1 : q (φ - (t : R)) = n := by
    have hl := q_line q para φ 1 (-t)
    rw [Int.cast_neg, mul_one, ← sub_eq_add_neg, add_comm φ 1, hn, ht, one] at hl
    rw [hl]; ring

  have h2 : q (φ * φ - (t : R) * φ) = n * n := by
    have e : φ * φ - (t : R) * φ = φ * (φ - (t : R)) := by
      rw [mul_sub, (Int.cast_commute t φ).eq]
    rw [e, mul, hn, h1]

  have h3 : q (1 - φ) = 1 - t + n := by
    have := para 1 φ; rw [ht, one, hn] at this; linarith

  have h4 : q (1 - φ * φ) = (1 + t + n) * (1 - t + n) := by
    have e : (1 - φ * φ : R) = (1 + φ) * (1 - φ) := by noncomm_ring
    rw [e, mul, ht, h3]

  have h5 : q (1 + φ * φ) = (n - 1) ^ 2 + t ^ 2 := by
    have := para 1 (φ * φ); rw [h4, mul, hn, one] at this; linear_combination this

  have h6 : q (1 + φ * φ + φ) = (n - 1) ^ 2 + t ^ 2 + n + t * (1 + n) := by
    have hl := q_line q para (1 + φ * φ) φ 2
    have e : (1 + φ * φ + ((2 : ℤ) : R) * φ) = (1 + φ) * (1 + φ) := by push_cast; noncomm_ring
    rw [e, mul, ht, h5, hn] at hl
    linarith

  have h7 : q (1 + φ * φ - (t : R) * φ) = (n - 1) ^ 2 := by
    have hl := q_line q para (1 + φ * φ) φ (-t)
    have e : (1 + φ * φ + ((-t : ℤ) : R) * φ) = 1 + φ * φ - (t : R) * φ := by
      rw [Int.cast_neg, neg_mul, ← sub_eq_add_neg]
    rw [e, h6, h5, hn] at hl
    rw [hl]; ring

  have hl := q_line q para (φ * φ - (t : R) * φ) 1 n
  rw [mul_one, show φ * φ - (t : R) * φ + 1 = 1 + φ * φ - (t : R) * φ by abel, h7, h2, one] at hl
  rw [hl]; ring

end Algebra

section XRep

variable {k : Type*} [Field k] [IsAlgClosed k] (W' : WeierstrassCurve k)

def XRep (α : W'.toAffine.Point → W'.toAffine.Point) (u v : k[X]) : Prop :=
  IsCoprime u v ∧ v.natDegree < u.natDegree ∧ ∃ B : Set k, B.Finite ∧
    ∀ (x y : k) (h : W'.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W'.toAffine.Nonsingular x' y'),
        α (.some x y h) = .some x' y' h' ∧ x' * v.eval x = u.eval x

theorem exists_nonsingular [W'.IsElliptic] (x : k) : ∃ y, W'.toAffine.Nonsingular x y := by
  have hdeg : (W'.toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [Affine.monic_polynomial.degree_map, Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (W'.toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

variable {W'}

omit [IsAlgClosed k] in
theorem XRep.ne_zero {α : W'.toAffine.Point → W'.toAffine.Point} {u v : k[X]} (h : XRep W' α u v) :
    u ≠ 0 := by
  rintro rfl
  exact absurd h.2.1 (by simp)

theorem XRep.natDegree_eq [W'.IsElliptic] {α : W'.toAffine.Point → W'.toAffine.Point}
    {u v u' v' : k[X]} (h : XRep W' α u v) (h' : XRep W' α u' v') :
    u.natDegree = u'.natDegree := by
  obtain ⟨huv, hvu, B, hB, hrep⟩ := h
  obtain ⟨huv', hvu', B', hB', hrep'⟩ := h'

  have hpoly : u * v' = u' * v := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := (B ∪ B')ᶜ) ?_ ((hB.union hB').infinite_compl)
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
    obtain ⟨y, hy⟩ := exists_nonsingular W' x
    obtain ⟨x₁, y₁, h₁, e₁, r₁⟩ := hrep x y hy hx.1
    obtain ⟨x₂, y₂, h₂, e₂, r₂⟩ := hrep' x y hy hx.2
    rw [e₁] at e₂
    obtain ⟨rfl, -⟩ := (Affine.Point.some.injEq ..).mp e₂
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_mul]
    linear_combination v.eval x * r₂ - v'.eval x * r₁
  have h0 : u ≠ 0 := XRep.ne_zero ⟨huv, hvu, B, hB, hrep⟩
  have h0' : u' ≠ 0 := XRep.ne_zero ⟨huv', hvu', B', hB', hrep'⟩
  have d1 : u ∣ u' := huv.dvd_of_dvd_mul_right ⟨v', by rw [hpoly]⟩
  have d2 : u' ∣ u := huv'.dvd_of_dvd_mul_right ⟨v, by rw [← hpoly]⟩
  exact le_antisymm (natDegree_le_of_dvd d1 h0') (natDegree_le_of_dvd d2 h0)

theorem XRep.apply_ne_zero [W'.IsElliptic] {α : W'.toAffine.Point → W'.toAffine.Point} {u v : k[X]}
    (h : XRep W' α u v) : ∃ P, α P ≠ 0 := by
  obtain ⟨-, -, B, hB, hrep⟩ := h
  obtain ⟨x, hx⟩ := hB.infinite_compl.nonempty
  obtain ⟨y, hy⟩ := exists_nonsingular W' x
  obtain ⟨x', y', h', e, -⟩ := hrep x y hy hx
  exact ⟨_, by rw [e]; exact Affine.Point.some_ne_zero h'⟩

variable (W')

open Classical in

noncomputable def deg (α : W'.toAffine.Point → W'.toAffine.Point) : ℕ :=
  if h : ∃ uv : k[X] × k[X], XRep W' α uv.1 uv.2 then h.choose.1.natDegree else 0

variable {W'}

theorem deg_eq [W'.IsElliptic] {α : W'.toAffine.Point → W'.toAffine.Point} {u v : k[X]}
    (h : XRep W' α u v) : deg W' α = u.natDegree := by
  classical
  have hex : ∃ uv : k[X] × k[X], XRep W' α uv.1 uv.2 := ⟨(u, v), h⟩
  rw [deg, dif_pos hex]
  exact hex.choose_spec.natDegree_eq h

theorem deg_zero_fun [W'.IsElliptic] {α : W'.toAffine.Point → W'.toAffine.Point} (hα : ∀ P, α P = 0) :
    deg W' α = 0 := by
  classical
  rw [deg, dif_neg]
  rintro ⟨uv, h⟩
  obtain ⟨P, hP⟩ := h.apply_ne_zero
  exact hP (hα P)

theorem deg_pos [W'.IsElliptic] {α : W'.toAffine.Point → W'.toAffine.Point} {u v : k[X]}
    (h : XRep W' α u v) : 0 < deg W' α := by
  rw [deg_eq h]; exact lt_of_le_of_lt (Nat.zero_le _) h.2.1

omit [IsAlgClosed k] in

theorem xRep_id : XRep W' id X 1 :=
  ⟨isCoprime_one_right, by simp, ∅, Set.finite_empty, fun x y h _ => ⟨x, y, h, rfl, by simp⟩⟩

omit [IsAlgClosed k] in

theorem XRep.neg {α : W'.toAffine.Point → W'.toAffine.Point} {u v : k[X]} (h : XRep W' α u v) :
    XRep W' (fun P => -α P) u v := by
  obtain ⟨huv, hvu, B, hB, hrep⟩ := h
  refine ⟨huv, hvu, B, hB, fun x y hxy hx => ?_⟩
  obtain ⟨x', y', h', e, r⟩ := hrep x y hxy hx
  exact ⟨x', W'.toAffine.negY x' y', (Affine.nonsingular_neg ..).mpr h',
    by change -α (.some x y hxy) = _; rw [e]; rfl, r⟩

theorem XRep.comp {α β : W'.toAffine.Point → W'.toAffine.Point} {u v s t : k[X]}
    (hα : XRep W' α u v) (hβ : XRep W' β s t) :
    ∃ U V : k[X], XRep W' (β ∘ α) U V ∧ U.natDegree = u.natDegree * s.natDegree := by
  obtain ⟨huv, hvu, B, hB, hrepα⟩ := hα
  obtain ⟨hst, hts, B', hB', hrepβ⟩ := hβ
  obtain ⟨U, V, B'', hUV, hVU, hdeg, hB'', hrep⟩ :=
    WeierstrassCurve.exists_xCoord_rep_comp W' W' W' α β huv hvu hB hrepα hst hts hB' hrepβ
  exact ⟨U, V, ⟨hUV, hVU, B'', hB'', hrep⟩, hdeg⟩

omit [IsAlgClosed k] in

theorem xRep_two [DecidableEq k] [W'.IsElliptic] :
    XRep W' (fun P => (2 : ℤ) • P) (W'.Φ 2) (W'.ΨSq 2) := by
  have hΨ : W'.ΨSq 2 ≠ 0 := by rw [ΨSq_two]; exact W'.Psi2Sq_ne_zero_of_isElliptic
  refine ⟨W'.isCoprime_Phi_PsiSq 2, ?_, {x | (W'.ΨSq 2).IsRoot x},
    Polynomial.finite_setOf_isRoot hΨ, fun x y h hx => ?_⟩
  · rw [natDegree_Φ]
    exact lt_of_le_of_lt (W'.natDegree_ΨSq_le 2) (by norm_num)
  · simp only [Set.mem_setOf_eq, IsRoot.def] at hx
    have hψ : (W'.ψ 2).evalEval x y ≠ 0 := by
      intro h0
      have hsq := congr_arg (Polynomial.evalEval x y) W'.ψ₂_sq
      rw [evalEval_pow, ← ψ_two, h0, evalEval_add, evalEval_C, evalEval_mul, h.1, mul_zero,
        add_zero, ← ΨSq_two] at hsq
      exact hx (by simpa using hsq.symm)
    obtain ⟨y', h', e⟩ := Affine.Point.zsmul_some_eq_some_div W' h hψ
    exact ⟨_, y', h', e, div_mul_cancel₀ _ hx⟩

end XRep

section EndRing

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
  (W : WeierstrassCurve F) [W.IsElliptic]

abbrev Pt := (W.baseChange k).toAffine.Point

scoped instance : (W.baseChange k).IsElliptic := inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)

variable {k} in

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

omit [IsAlgClosed k] [DecidableEq k] in
theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : evalEvalBC k p x y = bc x y p := rfl

omit [IsAlgClosed k] [DecidableEq k] in
@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by simp [bc]

omit [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k}
    {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁} (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂ : (W.baseChange k).toAffine.Nonsingular x₂ y₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

omit [IsAlgClosed k] [W.IsElliptic] in

theorem neg_mem_rationalHomSet {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) :
    -α ∈ rationalHomSet k W W := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet k W W
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W.a₁) * nX * dY - C (C W.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  simp only [evalEvalBC_eq] at hdX hdY hP ⊢
  refine ⟨hdX, by rw [map_mul]; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (bc x y nX / bc x y dX)
        ((W.baseChange k).toAffine.negY (bc x y nX / bc x y dX) (bc x y nY / bc x y dY))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_some_of_eq k W hneg rfl ?_
  simp only [Affine.negY, map_sub, map_neg, map_mul, bc_CC]
  change -(bc x y nY / bc x y dY) - algebraMap F k W.a₁ * (bc x y nX / bc x y dX)
      - algebraMap F k W.a₃ = _
  field_simp

theorem mem_rationalHomSet_of_mem {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) :
    (φ : Pt k W →+ Pt k W) ∈ rationalHomSet k W W := by
  induction hφ using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact id_mem_rationalHomSet k W
  | add x y _ _ hx hy => exact WeierstrassCurve.add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet k W hx
  | mul x y _ _ hx hy => exact WeierstrassCurve.comp_mem_rationalHomSet k W W W hy hx

theorem exists_xRep {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) (hφ0 : φ ≠ 0) :
    ∃ u v : k[X], XRep (W.baseChange k) φ u v := by
  have hmem := mem_rationalHomSet_of_mem k W hφ
  obtain ⟨u, v, B, huv, hB, hrep⟩ :=
    WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet k W W hmem hφ0
  have hvu : v.natDegree < u.natDegree :=
    WeierstrassCurve.natDegree_lt_of_xCoord_rep (W.baseChange k) (W.baseChange k) φ huv hB hrep
  exact ⟨u, v, huv, hvu, B, hB, hrep⟩

noncomputable def d (φ : AddMonoid.End (Pt k W)) : ℤ := deg (W.baseChange k) φ

theorem d_zero : d k W 0 = 0 := by
  simp [d, deg_zero_fun]

theorem d_eq_zero {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) (h : d k W φ = 0) :
    φ = 0 := by
  by_contra hφ0
  obtain ⟨u, v, hr⟩ := exists_xRep k W hφ hφ0
  have := deg_pos hr
  simp [d] at h; omega

theorem d_one : d k W 1 = 1 := by
  have : XRep (W.baseChange k) ((1 : AddMonoid.End (Pt k W)) : Pt k W → Pt k W) X 1 := by
    rw [AddMonoid.End.coe_one]; exact xRep_id
  simp only [d, deg_eq this, natDegree_X, Nat.cast_one]

theorem d_neg (φ : AddMonoid.End (Pt k W)) (hφ : φ ∈ rationalEndSubring k W) : d k W (-φ) = d k W φ := by
  by_cases hφ0 : φ = 0
  · rw [hφ0, neg_zero]
  obtain ⟨u, v, hr⟩ := exists_xRep k W hφ hφ0
  have hn : XRep (W.baseChange k) ((-φ : AddMonoid.End (Pt k W)) : Pt k W → Pt k W) u v := hr.neg
  simp only [d, deg_eq hr, deg_eq hn]

theorem d_mul (φ ψ : AddMonoid.End (Pt k W)) (hφ : φ ∈ rationalEndSubring k W)
    (hψ : ψ ∈ rationalEndSubring k W) : d k W (φ * ψ) = d k W φ * d k W ψ := by
  by_cases hφ0 : φ = 0
  · rw [hφ0, zero_mul, d_zero, zero_mul]
  by_cases hψ0 : ψ = 0
  · rw [hψ0, mul_zero, d_zero, mul_zero]
  obtain ⟨u, v, hrφ⟩ := exists_xRep k W hφ hφ0
  obtain ⟨s, t, hrψ⟩ := exists_xRep k W hψ hψ0
  obtain ⟨U, V, hr, hdeg⟩ := hrψ.comp hrφ
  have hr' : XRep (W.baseChange k) ((φ * ψ : AddMonoid.End (Pt k W)) : Pt k W → Pt k W) U V := by
    rw [AddMonoid.End.coe_mul]; exact hr
  simp only [d, deg_eq hr', deg_eq hrφ, deg_eq hrψ, hdeg]
  push_cast; ring

theorem d_two : d k W 2 = 4 := by
  have h2 : XRep (W.baseChange k) ((2 : AddMonoid.End (Pt k W)) : Pt k W → Pt k W)
      ((W.baseChange k).Φ 2) ((W.baseChange k).ΨSq 2) := by
    have e : ((2 : AddMonoid.End (Pt k W)) : Pt k W → Pt k W) = fun P => (2 : ℤ) • P := by
      ext P
      change ((2 : ℕ) : AddMonoid.End (Pt k W)) P = _
      rw [AddMonoid.End.natCast_apply]; norm_cast
    rw [e]; exact xRep_two
  simp only [d, deg_eq h2, natDegree_Φ]; norm_num

theorem d_para (φ ψ : AddMonoid.End (Pt k W)) (hφ : φ ∈ rationalEndSubring k W)
    (hψ : ψ ∈ rationalEndSubring k W) :
    d k W (φ + ψ) + d k W (φ - ψ) = 2 * d k W φ + 2 * d k W ψ := by
  by_cases hφ0 : φ = 0
  · rw [hφ0, zero_add, zero_sub, d_zero, d_neg k W ψ hψ]; ring
  by_cases hψ0 : ψ = 0
  · rw [hψ0, add_zero, sub_zero, d_zero]; ring
  by_cases hp0 : φ + ψ = 0
  · have hψe : ψ = -φ := (neg_eq_of_add_eq_zero_right hp0).symm
    rw [hp0, hψe, sub_neg_eq_add, ← two_mul φ, d_mul k W 2 φ (ofNat_mem _ 2) hφ, d_two,
      d_neg k W φ hφ, d_zero]; ring
  by_cases hm0 : φ - ψ = 0
  · have hψe : ψ = φ := (sub_eq_zero.mp hm0).symm
    rw [hm0, hψe, ← two_mul φ, d_mul k W 2 φ (ofNat_mem _ 2) hφ, d_two, d_zero]; ring

  obtain ⟨u, v, hrφ⟩ := exists_xRep k W hφ hφ0
  obtain ⟨s, t, hrψ⟩ := exists_xRep k W hψ hψ0
  obtain ⟨u₁, v₁, hrp⟩ := exists_xRep k W (add_mem hφ hψ) hp0
  obtain ⟨u₂, v₂, hrm⟩ := exists_xRep k W (sub_mem hφ hψ) hm0
  rw [d, d, d, d, deg_eq hrφ, deg_eq hrψ, deg_eq hrp, deg_eq hrm]
  obtain ⟨huv, hvu, B, hB, hrepφ⟩ := hrφ
  obtain ⟨hst, hts, B', hB', hrepψ⟩ := hrψ
  obtain ⟨huv₁, hvu₁, B₁, hB₁, hrepp⟩ := hrp
  obtain ⟨huv₂, hvu₂, B₂, hB₂, hrepm⟩ := hrm
  have hv0 : ∀ {u v : k[X]}, IsCoprime u v → v.natDegree < u.natDegree → v ≠ 0 := by
    rintro u v huv hvu rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp huv)
    omega
  have key := Affine.Point.natDegree_parallelogram_law (W.baseChange k)
    ((hB.union hB').union (hB₁.union hB₂)) huv hst huv₁ huv₂
    (XRep.ne_zero ⟨huv, hvu, B, hB, hrepφ⟩) (hv0 huv hvu) (hv0 hst hts) (hv0 huv₁ hvu₁)
    (hv0 huv₂ hvu₂) hvu.le hts ?_
  · have := key.2.2.1; zify at this; linear_combination this
  intro x hx
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular (W.baseChange k) x
  obtain ⟨xa, ya, ha, ea, ra⟩ := hrepφ x y hy hx.1.1
  obtain ⟨xb, yb, hb, eb, rb⟩ := hrepψ x y hy hx.1.2
  obtain ⟨xp, yp, hp, ep, rp⟩ := hrepp x y hy hx.2.1
  obtain ⟨xm, ym, hm, em, rm⟩ := hrepm x y hy hx.2.2
  refine ⟨xa, ya, xb, yb, xp, yp, xm, ym, ha, hb, hp, hm, ?_, ?_, ra, rb, rp, rm⟩
  · rw [← ea, ← eb, ← ep]; rfl
  · rw [← ea, ← eb, ← em]; rfl

end EndRing

section Assembly

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
  (W : WeierstrassCurve F) [W.IsElliptic]

theorem dualIsogenyExistence : DualIsogenyExistence (rationalEndSubring k W) := by
  intro φ hφ
  let S := rationalEndSubring k W
  let q : S → ℤ := fun x => d k W x.1
  have para : ∀ a b : S, q (a + b) + q (a - b) = 2 * q a + 2 * q b :=
    fun a b => d_para k W a.1 b.1 a.2 b.2
  have one : q 1 = 1 := d_one k W
  have mul : ∀ a b : S, q (a * b) = q a * q b := fun a b => d_mul k W a.1 b.1 a.2 b.2
  obtain ⟨n, hn⟩ : ∃ n : ℤ, q ⟨φ, hφ⟩ = n := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, q (1 + ⟨φ, hφ⟩) - 1 - n = t := ⟨_, rfl⟩

  have hchar := q_charPoly q para one mul ⟨φ, hφ⟩ n t hn (by rw [← ht]; ring)
  have hzero := d_eq_zero k W (SetLike.coe_mem _) hchar
  have hrel : φ * φ - (t : AddMonoid.End (Pt k W)) * φ + (n : AddMonoid.End (Pt k W)) = 0 := by
    push_cast at hzero; exact hzero
  refine ⟨AddMonoid.End.DualEndData.ofCharPoly φ t n hrel, ?_, ?_⟩
  ·
    rw [AddMonoid.End.DualEndData.ofCharPoly_dual]
    exact sub_mem (intCast_mem _ t) hφ
  ·
    rw [AddMonoid.End.DualEndData.ofCharPoly_norm, ← hn]
    exact Int.natCast_nonneg _

end Assembly

end WeierstrassCurve.DualExist
p2m_reactivate "P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring.WeierstrassCurve P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring.WeierstrassCurve.DualExist"
p2m_reactivate "P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] : DualIsogenyExistence (WeierstrassCurve.rationalEndSubring k W) :=
  WeierstrassCurve.DualExist.dualIsogenyExistence k W

end S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
end P2MW
export P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring (solution)
