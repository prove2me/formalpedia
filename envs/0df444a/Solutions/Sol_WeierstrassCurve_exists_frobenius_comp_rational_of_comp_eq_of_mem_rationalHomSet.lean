-- Prove2me | solution 1 for WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/736788ff-0a03-5e2a-a321-aefe13d9a8fe

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne a₃ a₁ map C_Ψ₂Sq Ψ₂Sq Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj Affine.negY_negY Affine.map_polynomial toAffine Affine.Point Affine.evalEval_polynomialY Affine.natDegree_polynomial ψ₂ Affine.nonsingular_neg Affine.monic_polynomial Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet surjective_of_mem_rationalHomSet Psi2Sq_ne_zero_of_isElliptic"
namespace FrobRational
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem bc_eq_evalEval (p : F[X][Y]) (x y : k) :
    bc x y p = (p.map (mapRingHom (algebraMap F k))).evalEval x y := by
  simp [bc]

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = bc x y p := by
  rw [bc_eq_evalEval]; rfl

@[scoped simp] theorem bc_C (x y : k) (q : F[X]) : bc x y (C q) = aeval x q := by
  simp [bc, Polynomial.map_C, eval_map_algebraMap]

@[scoped simp] theorem bc_Y (x y : k) : bc x y (Y : F[X][Y]) = y := by
  simp [bc]

theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp

theorem bc_CX (x y : k) : bc x y (C X : F[X][Y]) = x := by
  simp

theorem bc_polynomial (W : WeierstrassCurve F) {x y : k}
    (h : (W.baseChange k).toAffine.Equation x y) : bc x y W.toAffine.polynomial = 0 := by
  rw [bc_eq_evalEval]
  have hmap : W.toAffine.polynomial.map (mapRingHom (algebraMap F k)) =
      (W.baseChange k).toAffine.polynomial :=
    (WeierstrassCurve.Affine.map_polynomial W.toAffine (algebraMap F k)).symm
  rw [hmap]
  exact h

theorem exists_linear_rep (W : WeierstrassCurve F) (p : F[X][Y]) :
    ∃ p₀ p₁ : F[X], ∀ x y : k, (W.baseChange k).toAffine.Equation x y →
      bc x y p = aeval x p₀ + aeval x p₁ * y := by
  set f : F[X][Y] := W.toAffine.polynomial with hf
  have hmonic : f.Monic := WeierstrassCurve.Affine.monic_polynomial
  refine ⟨(p %ₘ f).coeff 0, (p %ₘ f).coeff 1, fun x y hxy => ?_⟩
  have hdeg : (p %ₘ f).natDegree ≤ 1 := by
    have h2 : f.natDegree = 2 := WeierstrassCurve.Affine.natDegree_polynomial
    have hf1 : f ≠ 1 := by
      intro h1
      rw [h1, natDegree_one] at h2
      exact absurd h2 (by norm_num)
    have := Polynomial.natDegree_modByMonic_lt p hmonic hf1
    omega
  set a := (p %ₘ f).coeff 1 with ha
  set b := (p %ₘ f).coeff 0 with hb
  have hrem : p %ₘ f = C a * Y + C b :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have hf0 : bc x y f = 0 := bc_polynomial (k := k) W hxy
  have hp : bc x y p = bc x y (p %ₘ f) + bc x y f * bc x y (p /ₘ f) := by
    rw [← map_mul, ← map_add, Polynomial.modByMonic_add_div]
  rw [hp, hf0, zero_mul, add_zero, hrem, map_add, map_mul, bc_C, bc_Y, bc_C]
  ring

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Generic

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : Pt k W | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : Pt k W) (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
      {P : Pt k W | ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

theorem finite_fibre (c : k) :
    {P : Pt k W | ∃ (y : k) (h : (W.baseChange k).toAffine.Nonsingular c y),
      P = .some c y h}.Finite := by
  have hfin : (⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation c y},
      {P : Pt k W | ∃ h : (W.baseChange k).toAffine.Nonsingular c y, P = .some c y h}).Finite := by
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W c) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  rintro P ⟨y, h, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨y, h.left, h, rfl⟩

theorem exists_nonsingular [IsAlgClosed k] [W.IsElliptic] (x : k) :
    ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
      WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

theorem finite_twoTorsionX [W.IsElliptic] :
    {x : k | ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y ∧
      y = (W.baseChange k).toAffine.negY x y}.Finite := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hne : (W.baseChange k).Ψ₂Sq ≠ 0 :=
    WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic (W.baseChange k)
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  rintro x ⟨y, h, hy⟩
  simp only [Set.mem_setOf_eq, IsRoot.def]
  have hE : (W.baseChange k).toAffine.polynomial.evalEval x y = 0 := h.left
  have hC := congrArg (evalEvalRingHom x y) (WeierstrassCurve.C_Ψ₂Sq (W.baseChange k))
  rw [map_sub, map_mul, map_pow] at hC
  simp only [coe_evalEvalRingHom, evalEval_C] at hC
  have hψ : ((W.baseChange k).ψ₂).evalEval x y = 2 * y + (W.baseChange k).a₁ * x +
      (W.baseChange k).a₃ :=
    WeierstrassCurve.Affine.evalEval_polynomialY x y
  have h4 : (4 : Polynomial (Polynomial k)).evalEval x y = 4 := by
    have := evalEval_natCast x y 4
    exact_mod_cast this
  rw [hC, hψ, hE, h4]
  have hy' : 2 * y + (W.baseChange k).a₁ * x + (W.baseChange k).a₃ = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  rw [hy']
  ring

end Generic

section Coord

variable {W : WeierstrassCurve F}

def xc : Pt k W → k
  | 0 => 0
  | .some x _ _ => x

def yc : Pt k W → k
  | 0 => 0
  | .some _ y _ => y

def nyc : Pt k W → k
  | 0 => 0
  | .some x y _ => (W.baseChange k).toAffine.negY x y

@[scoped simp] theorem xc_some {x y : k} (h : (W.baseChange k).toAffine.Nonsingular x y) :
    xc (.some x y h : Pt k W) = x := rfl

@[scoped simp] theorem yc_some {x y : k} (h : (W.baseChange k).toAffine.Nonsingular x y) :
    yc (.some x y h : Pt k W) = y := rfl

@[scoped simp] theorem nyc_some {x y : k} (h : (W.baseChange k).toAffine.Nonsingular x y) :
    nyc (.some x y h : Pt k W) = (W.baseChange k).toAffine.negY x y := rfl

@[scoped simp] theorem xc_neg (P : Pt k W) : xc (-P) = xc P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

@[scoped simp] theorem yc_neg (P : Pt k W) : yc (-P) = nyc P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

@[scoped simp] theorem nyc_neg (P : Pt k W) : nyc (-P) = yc P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [WeierstrassCurve.Affine.Point.neg_some, nyc_some, yc_some,
      WeierstrassCurve.Affine.negY_negY]

theorem some_eq_or_eq_neg {x y y' : k} (h : (W.baseChange k).toAffine.Nonsingular x y)
    (h' : (W.baseChange k).toAffine.Nonsingular x y') :
    (.some x y' h' : Pt k W) = .some x y h ∨ (.some x y' h' : Pt k W) = -.some x y h := by
  by_cases hv : y' = (W.baseChange k).toAffine.negY x y
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some]
    subst hv
    rfl
  · left
    have := WeierstrassCurve.Affine.Y_eq_of_Y_ne h'.left h.left rfl hv
    subst this
    rfl

theorem even_apply_eq {E : Pt k W → k} (hE : ∀ P, E (-P) = E P) {x y y' : k}
    (h : (W.baseChange k).toAffine.Nonsingular x y)
    (h' : (W.baseChange k).toAffine.Nonsingular x y') :
    E (.some x y' h') = E (.some x y h) := by
  rcases some_eq_or_eq_neg (k := k) h h' with e | e
  · rw [e]
  · rw [e, hE]

end Coord

section Descent

variable (W : WeierstrassCurve F) [IsAlgClosed k] [W.IsElliptic]

theorem descend_even (a b : F[X][Y]) {B : Set k} (hB : B.Finite)
    (hb : ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B → bc x y b ≠ 0)
    (heven : ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B →
      bc x y a / bc x y b = bc x ((W.baseChange k).toAffine.negY x y) a /
        bc x ((W.baseChange k).toAffine.negY x y) b) :
    ∃ (c d : F[X]) (B' : Set k), B'.Finite ∧
      ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B' →
        aeval x d ≠ 0 ∧ bc x y a / bc x y b = aeval x c / aeval x d := by
  obtain ⟨a₀, a₁, ha⟩ := exists_linear_rep (k := k) W a
  obtain ⟨b₀, b₁, hb'⟩ := exists_linear_rep (k := k) W b

  have hkey : a₁ * b₀ = a₀ * b₁ := by
    by_contra hne
    have hR : a₁ * b₀ - a₀ * b₁ ≠ 0 := sub_ne_zero.mpr hne
    have hRk : (a₁ * b₀ - a₀ * b₁).map (algebraMap F k) ≠ 0 := Polynomial.map_ne_zero hR
    have hfin : (B ∪ {x | ((a₁ * b₀ - a₀ * b₁).map (algebraMap F k)).IsRoot x} ∪
        {x : k | ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y ∧
          y = (W.baseChange k).toAffine.negY x y}).Finite :=
      (hB.union (Polynomial.finite_setOf_isRoot hRk)).union (finite_twoTorsionX (k := k) W)
    obtain ⟨x, hx⟩ := hfin.exists_notMem
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at hx
    obtain ⟨⟨hxB, hxR⟩, hx2⟩ := hx
    obtain ⟨y, hy⟩ := exists_nonsingular (k := k) W x
    have hy' : (W.baseChange k).toAffine.Nonsingular x ((W.baseChange k).toAffine.negY x y) :=
      (Affine.nonsingular_neg x y).mpr hy
    have hyy' : y ≠ (W.baseChange k).toAffine.negY x y := hx2 y hy
    have h1 := hb x y hy hxB
    have h2 := hb x _ hy' hxB
    have h3 := heven x y hy hxB
    rw [hb' x y hy.left] at h1
    rw [hb' x _ hy'.left] at h2
    rw [ha x y hy.left, ha x _ hy'.left, hb' x y hy.left, hb' x _ hy'.left,
      div_eq_div_iff h1 h2] at h3
    apply hxR
    simp only [IsRoot.def, eval_map_algebraMap, map_sub, map_mul]
    have h4 : (aeval x a₁ * aeval x b₀ - aeval x a₀ * aeval x b₁) *
        (y - (W.baseChange k).toAffine.negY x y) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hyy'
  by_cases hb1 : b₁ = 0
  ·
    have hb0 : b₀ ≠ 0 := by
      intro hb0
      obtain ⟨x, hx⟩ := hB.exists_notMem
      obtain ⟨y, hy⟩ := exists_nonsingular (k := k) W x
      apply hb x y hy hx
      rw [hb' x y hy.left, hb0, hb1]
      simp
    have ha1 : a₁ = 0 := by
      rw [hb1, mul_zero] at hkey
      exact (mul_eq_zero.mp hkey).resolve_right hb0
    refine ⟨a₀, b₀, B, hB, fun x y hy hx => ?_⟩
    have h1 := hb x y hy hx
    rw [hb' x y hy.left, hb1, map_zero, zero_mul, add_zero] at h1
    refine ⟨h1, ?_⟩
    rw [ha x y hy.left, hb' x y hy.left, ha1, hb1]
    simp
  · refine ⟨a₁, b₁, B ∪ {x | (b₁.map (algebraMap F k)).IsRoot x},
      hB.union (Polynomial.finite_setOf_isRoot (Polynomial.map_ne_zero hb1)),
      fun x y hy hx => ?_⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, IsRoot.def, eval_map_algebraMap] at hx
    obtain ⟨hxB, hxb⟩ := hx
    refine ⟨hxb, ?_⟩
    have h1 := hb x y hy hxB
    rw [hb' x y hy.left] at h1
    rw [ha x y hy.left, hb' x y hy.left, div_eq_div_iff h1 hxb]
    have hk := congrArg (aeval x) hkey
    simp only [map_mul] at hk
    linear_combination (-1 : k) * hk

end Descent

section Hom

variable [DecidableEq k] {W₁ W₂ : WeierstrassCurve F}

def Repr (α : Pt k W₁ →+ Pt k W₂) (nX dX nY dY : F[X][Y]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
    bc x y dX ≠ 0 ∧ bc x y dY ≠ 0 ∧
      ∃ h', α (.some x y h) = .some (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) h'

theorem repr_of_mem {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂)
    (hα0 : α ≠ 0) : ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧ Repr α nX dX nY dY B := by
  rcases hα with h | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · exact absurd h hα0
  · exact ⟨nX, dX, nY, dY, B, hB, hrep⟩

theorem ker_subset_not_good {α : Pt k W₁ →+ Pt k W₂} {nX dX nY dY : F[X][Y]} {B : Set k}
    (hrep : Repr α nX dX nY dY B) : {P | α P = 0} ⊆ {P | ¬ Good W₁ B P} := by
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

omit [DecidableEq k] in

theorem finite_preimage {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hker : {a | f a = 0}.Finite) {T : Set B} (hT : T.Finite) : (f ⁻¹' T).Finite := by
  have hT' : f ⁻¹' T = ⋃ t ∈ T, f ⁻¹' {t} := by
    ext a; simp
  rw [hT']
  refine hT.biUnion fun t _ => ?_
  by_cases ht : ∃ a, f a = t
  · obtain ⟨a, rfl⟩ := ht
    refine (hker.image fun c => a + c).subset ?_
    intro b hb
    refine ⟨b - a, ?_, by simp⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    simp [map_sub, hb]
  · refine Set.finite_empty.subset ?_
    intro b hb
    exact ht ⟨b, hb⟩

theorem xc_apply {α : Pt k W₁ →+ Pt k W₂} {nX dX nY dY : F[X][Y]} {B : Set k}
    (hrep : Repr α nX dX nY dY B) {x y : k} (h : (W₁.baseChange k).toAffine.Nonsingular x y)
    (hx : x ∉ B) : xc (α (.some x y h)) = bc x y nX / bc x y dX := by
  obtain ⟨-, -, h', e⟩ := hrep x y h hx
  rw [e, xc_some]

theorem xc_apply_even {α : Pt k W₁ →+ Pt k W₂} {nX dX nY dY : F[X][Y]} {B : Set k}
    (hrep : Repr α nX dX nY dY B) {x y : k} (h : (W₁.baseChange k).toAffine.Nonsingular x y)
    (hx : x ∉ B) :
    bc x y nX / bc x y dX = bc x ((W₁.baseChange k).toAffine.negY x y) nX /
      bc x ((W₁.baseChange k).toAffine.negY x y) dX := by
  have h' : (W₁.baseChange k).toAffine.Nonsingular x ((W₁.baseChange k).toAffine.negY x y) :=
    (Affine.nonsingular_neg x y).mpr h
  rw [← xc_apply hrep h hx, ← xc_apply hrep h' hx]
  exact (even_apply_eq (E := fun P => xc (α P)) (fun P => by simp [map_neg]) h h').symm

end Hom

section Main

variable [DecidableEq k] [IsAlgClosed k] {W₁ W₂ W₃ : WeierstrassCurve F}
  [W₁.IsElliptic] [W₂.IsElliptic]

noncomputable def Az (W₂ W₃ : WeierstrassCurve F) (rX sX rY sY pX qX pY qY : F[X][Y]) : F[X][Y] :=
  rY * pY * sX * qX + (rY * sX + C (C W₂.a₁) * rX * sY + C (C W₂.a₃) * sX * sY) *
    (pY * qX + C (C W₃.a₁) * pX * qY + C (C W₃.a₃) * qX * qY)

omit [DecidableEq k] [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic] in
theorem bc_Az_div {x y : k} (rX sX rY sY pX qX pY qY : F[X][Y]) (hsX : bc x y sX ≠ 0)
    (hsY : bc x y sY ≠ 0) (hqX : bc x y qX ≠ 0) (hqY : bc x y qY ≠ 0) :
    bc x y (Az W₂ W₃ rX sX rY sY pX qX pY qY) / bc x y (sX * sY * qX * qY) =
      bc x y rY / bc x y sY * (bc x y pY / bc x y qY) +
        (W₂.baseChange k).toAffine.negY (bc x y rX / bc x y sX) (bc x y rY / bc x y sY) *
          (W₃.baseChange k).toAffine.negY (bc x y pX / bc x y qX) (bc x y pY / bc x y qY) := by
  have e₁ : (W₂.baseChange k).toAffine.a₁ = algebraMap F k W₂.a₁ := rfl
  have e₂ : (W₂.baseChange k).toAffine.a₃ = algebraMap F k W₂.a₃ := rfl
  have e₃ : (W₃.baseChange k).toAffine.a₁ = algebraMap F k W₃.a₁ := rfl
  have e₄ : (W₃.baseChange k).toAffine.a₃ = algebraMap F k W₃.a₃ := rfl
  simp only [Az, map_add, map_mul, bc_CC, Affine.negY, e₁, e₂, e₃, e₄]
  field_simp
  ring

theorem main {ρ : Pt k W₁ →+ Pt k W₂} {ψ : Pt k W₁ →+ Pt k W₃}
    (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet k W₁ W₃) (hψ0 : ψ ≠ 0)
    {μ : Pt k W₂ →+ Pt k W₃} (hμ : μ.comp ρ = ψ) :
    ∃ (t : ℕ) (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : (W₂.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        bc x y dX ≠ 0 ∧ bc x y dY ≠ 0 ∧
          ∃ (x' y' : k) (h' : (W₃.baseChange k).toAffine.Nonsingular x' y'),
            μ (.some x y h) = .some x' y' h' ∧
              x' ^ ringExpChar F ^ t = bc x y nX / bc x y dX ∧
              y' ^ ringExpChar F ^ t = bc x y nY / bc x y dY := by

  obtain ⟨q, hqF⟩ := ExpChar.exists F
  have hpeq : ringExpChar F = q := ringExpChar.eq F q
  haveI : ExpChar k q := expChar_of_injective_algebraMap (algebraMap F k).injective q
  rw [hpeq]
  have hμρ : ∀ P, μ (ρ P) = ψ P := fun P => by rw [← AddMonoidHom.comp_apply, hμ]

  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hψ0
    rw [← hμ, AddMonoidHom.comp_zero]
  obtain ⟨rX, sX, rY, sY, Bρ, hBρ, hrρ⟩ := repr_of_mem hρ hρ0
  obtain ⟨pX, qX, pY, qY, Bψ, hBψ, hrψ⟩ := repr_of_mem hψ hψ0

  have hkerψ : {P : Pt k W₁ | ψ P = 0}.Finite :=
    (finite_not_good W₁ hBψ).subset (ker_subset_not_good hrψ)
  have hkerρ : {P : Pt k W₁ | ρ P = 0}.Finite :=
    hkerψ.subset fun P (hP : ρ P = 0) => show ψ P = 0 by rw [← hμρ, hP, map_zero]
  have hsurj : Function.Surjective ρ :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hρ hρ0
  have hkerμ : {Q : Pt k W₂ | μ Q = 0}.Finite := by
    refine (hkerψ.image ρ).subset ?_
    intro Q hQ
    obtain ⟨P, rfl⟩ := hsurj Q
    exact ⟨P, by simpa [hμρ] using hQ, rfl⟩
  have hXμ : (xc '' {Q : Pt k W₂ | μ Q = 0}).Finite := hkerμ.image xc

  choose w hw using exists_nonsingular (k := k) W₁
  choose v₀ hv₀ using exists_nonsingular (k := k) W₂

  set Ex : Pt k W₂ → k := fun Q => xc (μ Q) with hEx
  set Ez : Pt k W₂ → k := fun Q => yc Q * yc (μ Q) + nyc Q * nyc (μ Q) with hEz
  have hEx_even : ∀ Q, Ex (-Q) = Ex Q := fun Q => by simp [hEx, map_neg]
  have hEz_even : ∀ Q, Ez (-Q) = Ez Q := fun Q => by
    simp only [hEz, map_neg, yc_neg, nyc_neg]; ring
  have hQ₀ : ∀ {E : Pt k W₂ → k}, (∀ Q, E (-Q) = E Q) →
      ∀ (u v : k) (h : (W₂.baseChange k).toAffine.Nonsingular u v),
        E (.some u (v₀ u) (hv₀ u)) = E (.some u v h) :=
    fun hE u v h => even_apply_eq hE h (hv₀ u)

  obtain ⟨fn, fd, Bf, hBf, hf⟩ := descend_even (k := k) W₁ rX sX hBρ
    (fun x y h hx => (hrρ x y h hx).1) (fun x y h hx => xc_apply_even hrρ h hx)
  obtain ⟨gn, gd, Bg, hBg, hg⟩ := descend_even (k := k) W₁ pX qX hBψ
    (fun x y h hx => (hrψ x y h hx).1) (fun x y h hx => xc_apply_even hrψ h hx)
  have hZρ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ Bρ ∪ Bψ →
      bc x y (sX * sY * qX * qY) ≠ 0 ∧
        bc x y (Az W₂ W₃ rX sX rY sY pX qX pY qY) / bc x y (sX * sY * qX * qY) =
          Ez (ρ (.some x y h)) := by
    intro x y h hx
    simp only [Set.mem_union, not_or] at hx
    obtain ⟨hsX, hsY, h₁, e₁⟩ := hrρ x y h hx.1
    obtain ⟨hqX, hqY, h₂, e₂⟩ := hrψ x y h hx.2
    refine ⟨by simp only [map_mul]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsX hsY) hqX) hqY,
      ?_⟩
    rw [bc_Az_div rX sX rY sY pX qX pY qY hsX hsY hqX hqY]
    simp only [hEz, hμρ]
    simp only [e₁, e₂, yc_some, nyc_some]
  obtain ⟨zn, zd, Bz, hBz, hz⟩ := descend_even (k := k) W₁ (Az W₂ W₃ rX sX rY sY pX qX pY qY)
    (sX * sY * qX * qY) (hBρ.union hBψ) (fun x y h hx => (hZρ x y h hx).1) (by
      intro x y h hx
      have h' : (W₁.baseChange k).toAffine.Nonsingular x ((W₁.baseChange k).toAffine.negY x y) :=
        (Affine.nonsingular_neg x y).mpr h
      rw [(hZρ x y h hx).2, (hZρ x _ h' hx).2]
      exact (even_apply_eq (E := fun P => Ez (ρ P))
        (fun P => by simp only [map_neg]; exact hEz_even _) h h').symm)

  have hfnc : ∀ c : F, fn ≠ C c * fd := by
    intro c hc
    have hfin : (ρ ⁻¹' {Q : Pt k W₂ | ∃ (y : k)
        (h : (W₂.baseChange k).toAffine.Nonsingular (algebraMap F k c) y),
          Q = .some (algebraMap F k c) y h}).Finite :=
      finite_preimage ρ hkerρ (finite_fibre (k := k) W₂ (algebraMap F k c))
    set P₀ : k → Pt k W₁ := fun x => .some x (w x) (hw x) with hP₀
    have hinj : Function.Injective P₀ := fun x x' e =>
      (WeierstrassCurve.Affine.Point.some.inj e).left
    have hsub : (Bρ ∪ Bf)ᶜ ⊆ P₀ ⁻¹' (ρ ⁻¹' {Q : Pt k W₂ | ∃ (y : k)
        (h : (W₂.baseChange k).toAffine.Nonsingular (algebraMap F k c) y),
          Q = .some (algebraMap F k c) y h}) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
      obtain ⟨hsX, -, h₁, e₁⟩ := hrρ x (w x) (hw x) hx.1
      obtain ⟨hfd, hfx⟩ := hf x (w x) (hw x) hx.2
      have hcx : bc x (w x) rX / bc x (w x) sX = algebraMap F k c := by
        rw [hfx, hc, map_mul, aeval_C, mul_div_assoc, div_self hfd, mul_one]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hP₀, e₁]
      refine ⟨bc x (w x) rY / bc x (w x) sY, hcx ▸ h₁, ?_⟩
      congr 1
    have hcfin : ((Bρ ∪ Bf)ᶜ).Finite :=
      ((hfin.preimage (hinj.injOn)).subset hsub)
    have huniv : (Set.univ : Set k).Finite := by
      rw [← Set.union_compl_self (Bρ ∪ Bf)]
      exact (hBρ.union hBf).union hcfin
    exact Set.infinite_univ huniv

  obtain ⟨t₁, hxn, hxd, T₁, hT₁, HX⟩ :=
    Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational k fn fd gn gd
      hfnc (fun u => Ex (.some u (v₀ u) (hv₀ u))) (Bρ ∪ Bψ ∪ Bf ∪ Bg)
      (((hBρ.union hBψ).union hBf).union hBg) (by
        intro x hx
        simp only [Set.mem_union, not_or] at hx
        obtain ⟨⟨⟨hxρ, hxψ⟩, hxf⟩, hxg⟩ := hx
        obtain ⟨hfd, hfx⟩ := hf x (w x) (hw x) hxf
        obtain ⟨hgd, hgx⟩ := hg x (w x) (hw x) hxg
        refine ⟨hfd, hgd, ?_⟩
        obtain ⟨hsX, hsY, h₁, e₁⟩ := hrρ x (w x) (hw x) hxρ
        rw [← hfx, ← hgx, hQ₀ hEx_even _ _ h₁, ← xc_apply hrψ (hw x) hxψ]
        simp only [hEx]
        rw [← e₁, hμρ])
  obtain ⟨t₂, hzn, hzd, T₂, hT₂, HZ⟩ :=
    Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational k fn fd zn zd
      hfnc (fun u => Ez (.some u (v₀ u) (hv₀ u))) (Bρ ∪ Bψ ∪ Bf ∪ Bz)
      (((hBρ.union hBψ).union hBf).union hBz) (by
        intro x hx
        simp only [Set.mem_union, not_or] at hx
        obtain ⟨⟨⟨hxρ, hxψ⟩, hxf⟩, hxz⟩ := hx
        obtain ⟨hfd, hfx⟩ := hf x (w x) (hw x) hxf
        obtain ⟨hzd', hzx⟩ := hz x (w x) (hw x) hxz
        refine ⟨hfd, hzd', ?_⟩
        obtain ⟨hsX, hsY, h₁, e₁⟩ := hrρ x (w x) (hw x) hxρ
        rw [← hfx, ← hzx, hQ₀ hEz_even _ _ h₁,
          (hZρ x (w x) (hw x) (fun hh => hh.elim hxρ hxψ)).2, e₁])

  have ea₁ : (W₂.baseChange k).toAffine.a₁ = algebraMap F k W₂.a₁ := rfl
  have ea₃ : (W₂.baseChange k).toAffine.a₃ = algebraMap F k W₂.a₃ := rfl
  have eb₁ : (W₃.baseChange k).toAffine.a₁ = algebraMap F k W₃.a₁ := rfl
  have eb₃ : (W₃.baseChange k).toAffine.a₃ = algebraMap F k W₃.a₃ := rfl
  set NB : F[X][Y] := -(Y : F[X][Y]) - C (C W₂.a₁ * X + C W₂.a₃) with hNBdef
  have hNB : ∀ u v : k, bc u v NB = (W₂.baseChange k).toAffine.negY u v := by
    intro u v
    rw [hNBdef, Affine.negY, ea₁, ea₃]
    simp only [map_sub, map_neg, map_add, map_mul, bc_Y, bc_C, aeval_C, aeval_X]
    ring
  set nY : F[X][Y] := C (hzn ^ q ^ t₁ * hxd ^ q ^ t₂) + NB ^ q ^ (t₁ + t₂) *
    (C (C (W₃.a₁ ^ q ^ (t₁ + t₂))) * C (hxn ^ q ^ t₂ * hzd ^ q ^ t₁) +
      C (C (W₃.a₃ ^ q ^ (t₁ + t₂))) * C (hxd ^ q ^ t₂ * hzd ^ q ^ t₁)) with hnYdef
  set dY : F[X][Y] := C (hzd ^ q ^ t₁ * hxd ^ q ^ t₂) * (Y - NB) ^ q ^ (t₁ + t₂) with hdYdef
  have hnY : ∀ u v : k, bc u v nY =
      aeval u hzn ^ q ^ t₁ * aeval u hxd ^ q ^ t₂ +
        (W₂.baseChange k).toAffine.negY u v ^ q ^ (t₁ + t₂) *
          (algebraMap F k W₃.a₁ ^ q ^ (t₁ + t₂) * (aeval u hxn ^ q ^ t₂ * aeval u hzd ^ q ^ t₁) +
            algebraMap F k W₃.a₃ ^ q ^ (t₁ + t₂) *
              (aeval u hxd ^ q ^ t₂ * aeval u hzd ^ q ^ t₁)) := by
    intro u v
    rw [hnYdef]
    simp only [map_add, map_mul, map_pow, bc_C, aeval_C, hNB]
  have hdY : ∀ u v : k, bc u v dY = aeval u hzd ^ q ^ t₁ * aeval u hxd ^ q ^ t₂ *
      (v - (W₂.baseChange k).toAffine.negY u v) ^ q ^ (t₁ + t₂) := by
    intro u v
    rw [hdYdef]
    simp only [map_sub, map_mul, map_pow, bc_C, bc_Y, hNB]
  refine ⟨t₁ + t₂, C (hxn ^ q ^ t₂), C (hxd ^ q ^ t₂), nY, dY,
    T₁ ∪ T₂ ∪ xc '' {Q : Pt k W₂ | μ Q = 0} ∪
      {x : k | ∃ y : k, (W₂.baseChange k).toAffine.Nonsingular x y ∧
        y = (W₂.baseChange k).toAffine.negY x y},
    ((hT₁.union hT₂).union hXμ).union (finite_twoTorsionX (k := k) W₂), ?_⟩
  intro u v h hu
  simp only [Set.mem_union, not_or] at hu
  obtain ⟨⟨⟨huT₁, huT₂⟩, huX⟩, hu2⟩ := hu
  obtain ⟨hD₁, hx2⟩ := HX u huT₁
  obtain ⟨hD₂, hz2⟩ := HZ u huT₂
  have hvv : v - (W₂.baseChange k).toAffine.negY u v ≠ 0 :=
    sub_ne_zero.mpr fun h2 => hu2 ⟨v, h, h2⟩
  have hμ0 : μ (.some u v h) ≠ 0 := fun e0 => huX ⟨.some u v h, e0, rfl⟩
  rcases e : μ (.some u v h) with _ | ⟨xμ, yμ, h'⟩
  · exact absurd e hμ0
  have hX1 : Ex (.some u v h) = xμ := by simp only [hEx, e, xc_some]
  have hZ1 : Ez (.some u v h) = v * yμ + (W₂.baseChange k).toAffine.negY u v *
      (W₃.baseChange k).toAffine.negY xμ yμ := by
    simp only [hEz, e, yc_some, nyc_some]
  simp only [hpeq] at hx2 hz2
  rw [hQ₀ hEx_even u v h, hX1, eq_div_iff hD₁] at hx2
  rw [hQ₀ hEz_even u v h, hZ1, eq_div_iff hD₂] at hz2
  set vb := (W₂.baseChange k).toAffine.negY u v with hvbdef
  set Zval := v * yμ + vb * (W₃.baseChange k).toAffine.negY xμ yμ with hZdef
  have XN : xμ ^ q ^ (t₁ + t₂) * aeval u hxd ^ q ^ t₂ = aeval u hxn ^ q ^ t₂ := by
    rw [pow_add, pow_mul, ← mul_pow, hx2]
  have ZN : Zval ^ q ^ (t₁ + t₂) * aeval u hzd ^ q ^ t₁ = aeval u hzn ^ q ^ t₁ := by
    rw [pow_add, mul_comm (q ^ t₁), pow_mul, ← mul_pow, hz2]
  have hlin : (v - vb) * yμ = Zval + vb * (algebraMap F k W₃.a₁ * xμ + algebraMap F k W₃.a₃) := by
    rw [hZdef, Affine.negY, eb₁, eb₃]
    ring
  have hfrob : (v - vb) ^ q ^ (t₁ + t₂) * yμ ^ q ^ (t₁ + t₂) =
      Zval ^ q ^ (t₁ + t₂) +
        vb ^ q ^ (t₁ + t₂) * algebraMap F k W₃.a₁ ^ q ^ (t₁ + t₂) * xμ ^ q ^ (t₁ + t₂) +
        vb ^ q ^ (t₁ + t₂) * algebraMap F k W₃.a₃ ^ q ^ (t₁ + t₂) := by
    have e2 := congrArg (fun z => z ^ q ^ (t₁ + t₂)) hlin
    simp only [mul_pow, add_pow_expChar_pow, mul_add] at e2
    linear_combination e2
  rw [hnY, hdY]
  refine ⟨by simp only [bc_C, map_pow]; exact pow_ne_zero _ hD₁,
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD₂) (pow_ne_zero _ hD₁)) (pow_ne_zero _ hvv),
    xμ, yμ, h', rfl, ?_, ?_⟩
  · simp only [bc_C, map_pow]
    rw [eq_div_iff (pow_ne_zero _ hD₁)]
    exact XN
  · rw [eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hD₂) (pow_ne_zero _ hD₁))
      (pow_ne_zero _ hvv))]
    linear_combination (aeval u hxd ^ q ^ t₂ * aeval u hzd ^ q ^ t₁) * hfrob +
      aeval u hxd ^ q ^ t₂ * ZN +
      (vb ^ q ^ (t₁ + t₂) * algebraMap F k W₃.a₁ ^ q ^ (t₁ + t₂) * aeval u hzd ^ q ^ t₁) * XN

end Main

end WeierstrassCurve.FrobRational
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet.WeierstrassCurve.FrobRational"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet.WeierstrassCurve"

open WeierstrassCurve.FrobRational in
theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic] {ρ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} {ψ : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hψ : ψ ∈ WeierstrassCurve.rationalHomSet k W₁ W₃) (hψ0 : ψ ≠ 0) {μ : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hμ : μ.comp ρ = ψ) : ∃ (t : ℕ) (nX dX nY dY : Polynomial (Polynomial F)) (B : Set k), B.Finite ∧ ∀ (x y : k) (h : (W₂.baseChange k).toAffine.Nonsingular x y), x ∉ B → WeierstrassCurve.evalEvalBC k dX x y ≠ 0 ∧ WeierstrassCurve.evalEvalBC k dY x y ≠ 0 ∧ ∃ (x' y' : k) (h' : (W₃.baseChange k).toAffine.Nonsingular x' y'), μ (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' ^ ringExpChar F ^ t = WeierstrassCurve.evalEvalBC k nX x y / WeierstrassCurve.evalEvalBC k dX x y ∧ y' ^ ringExpChar F ^ t = WeierstrassCurve.evalEvalBC k nY x y / WeierstrassCurve.evalEvalBC k dY x y := by
  obtain ⟨t, nX, dX, nY, dY, B, hB, H⟩ := main hρ hψ hψ0 hμ
  refine ⟨t, nX, dX, nY, dY, B, hB, fun x y h hx => ?_⟩
  simp only [evalEvalBC_eq]
  exact H x y h hx

end S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet (solution)
