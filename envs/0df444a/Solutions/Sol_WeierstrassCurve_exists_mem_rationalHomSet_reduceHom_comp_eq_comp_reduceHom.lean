-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fba1396f-18bc-5d86-8da1-fa2f1f5898c9

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_ValuationSubring_exists_eval_eq_zero_and_residue_eq
import Theorems.Thm_ValuationSubring_exists_root_mem_of_monic
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom

open Polynomial IsLocalRing
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.equation_neg a₃ a₁ map b₂ isElliptic_iff Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.degree_polynomial reduction map_id toAffine Affine.Point Affine.nonsingular_neg map_Δ map_a₆ Affine.monic_polynomial b₆ map_a₁ Affine.equation_iff_nonsingular map_a₄ Affine.Point.some_ne_zero Δ Affine.map_negY Affine.equation_iff map_a₂ b₄ map_a₃ evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet reduceHom Affine.Y_mem_of_X_mem map_residue_Δ_ne_zero_iff Affine.equation_residue Affine.nonsingular_residue reducePoint reducePoint_some_of_mem reducePoint_some_of_notMem exists_xCoord_rep_of_mem_rationalHomSet surjective_of_mem_rationalHomSet Psi2Sq_ne_zero_of_isElliptic"
namespace ReduceRationalHom
p2m_open "WeierstrassCurve"

section Field

variable {k : Type*} [Field k]

theorem some_congr {V : Affine k} {x₁ x₂ y₁ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem exists_some_of_eq {V : Affine k} {x₁ x₂ y₁ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.Nonsingular x₁ y₁} {P : V.Point} (hP : P = .some x₁ y₁ h₁) :
    ∃ h₂ : V.Nonsingular x₂ y₂, P = .some x₂ y₂ h₂ := by
  subst hx; subst hy; exact ⟨h₁, hP⟩

theorem evalEvalBC_self (p : k[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = p.evalEval x y := by
  unfold WeierstrassCurve.evalEvalBC
  rw [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

variable (V : Affine k)

theorem exists_evalEval_eq_linear (G : k[X][Y]) :
    ∃ p q : k[X], ∀ x y : k, V.Equation x y → G.evalEval x y = p.eval x + q.eval x * y := by
  set r : k[X][Y] := G %ₘ V.polynomial with hr_def
  have hne1 : V.polynomial ≠ 1 := by
    intro h
    have := V.natDegree_polynomial
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  have hr : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt G V.monic_polynomial hne1
    rw [V.natDegree_polynomial] at this
    exact Nat.lt_succ_iff.mp this
  refine ⟨r.coeff 0, r.coeff 1, fun x y hxy => ?_⟩
  have hG : r + V.polynomial * (G /ₘ V.polynomial) = G := modByMonic_add_div G V.polynomial
  have hreq : r = C (r.coeff 1) * Y + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have h0 : V.polynomial.evalEval x y = 0 := hxy
  have hr_eval : r.evalEval x y = (r.coeff 0).eval x + (r.coeff 1).eval x * y := by
    conv_lhs => rw [hreq]
    rw [evalEval_add, evalEval_mul, evalEval_C, evalEval_C, evalEval_X]
    ring
  rw [← hG, evalEval_add, evalEval_mul, h0, zero_mul, add_zero, hr_eval]

theorem sub_negY_sq {x y : k} (h : V.Equation x y) :
    (y - V.negY x y) ^ 2 = (WeierstrassCurve.Ψ₂Sq V).eval x := by
  rw [Affine.equation_iff] at h
  simp only [Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination 4 * h

theorem exists_nonsingular [IsAlgClosed k] [V.IsElliptic] (x : k) :
    ∃ y : k, V.Nonsingular x y := by
  have hdeg : (V.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
      WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (V.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

theorem finite_setOf_equation (x : k) : {y : k | V.Equation x y}.Finite := by
  have hne : (V.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

theorem finite_setOf_X_mem {B : Set k} (hB : B.Finite) :
    {P : V.Point | ∃ (x y : k) (h : V.Nonsingular x y), P = .some x y h ∧ x ∈ B}.Finite := by
  have hfin : (⋃ x ∈ B, ⋃ y ∈ {y : k | V.Equation x y},
      {P : V.Point | ∃ h : V.Nonsingular x y, P = .some x y h}).Finite := by
    refine hB.biUnion fun x _ => (finite_setOf_equation V x).biUnion fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  rintro P ⟨x, y, h, rfl, hx⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨x, hx, y, h.left, h, rfl⟩

variable {V}

variable [DecidableEq k] [IsAlgClosed k] {V₁ V₂ : WeierstrassCurve k} [V₁.IsElliptic]
  [V₂.IsElliptic]

theorem exists_xrep {α : V₁.toAffine.Point →+ V₂.toAffine.Point}
    (hα : α ∈ rationalHomSet k V₁ V₂) (hα0 : α ≠ 0) :
    ∃ (u v : k[X]) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : V₁.toAffine.Nonsingular x y), x ∉ B →
        v.eval x ≠ 0 ∧ ∃ (x' y' : k) (h' : V₂.toAffine.Nonsingular x' y'),
          α (.some x y h) = .some x' y' h' ∧ x' = u.eval x / v.eval x := by
  obtain ⟨u, v, B, hcop, hB, H⟩ :=
    WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet k V₁ V₂ hα hα0
  refine ⟨u, v, B, hB, fun x y h hx => ?_⟩
  obtain ⟨x', y', h', hP, hx'⟩ := H x y h hx
  have hv : v.eval x ≠ 0 := by
    intro hv
    rw [hv, mul_zero] at hx'
    obtain ⟨s, t, hst⟩ := hcop
    have := congr_arg (eval x) hst
    rw [eval_add, eval_mul, eval_mul, ← hx', hv, eval_one, mul_zero, mul_zero, add_zero] at this
    exact zero_ne_one this
  exact ⟨hv, x', y', h', hP, by rw [eq_div_iff hv, hx']⟩

omit [IsAlgClosed k] [V₁.IsElliptic] [V₂.IsElliptic] in

theorem exists_rawrep {α : V₁.toAffine.Point →+ V₂.toAffine.Point}
    (hα : IsRationallyRepresented k V₁ V₂ α) :
    ∃ (nX dX nY dY : k[X][Y]) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : V₁.toAffine.Nonsingular x y), x ∉ B →
        dX.evalEval x y ≠ 0 ∧ dY.evalEval x y ≠ 0 ∧
          ∃ h', α (.some x y h) =
            .some (nX.evalEval x y / dX.evalEval x y) (nY.evalEval x y / dY.evalEval x y) h' := by
  obtain ⟨nX, dX, nY, dY, B, hB, H⟩ := hα
  exact ⟨nX.map (mapRingHom (algebraMap k k)), dX.map (mapRingHom (algebraMap k k)),
    nY.map (mapRingHom (algebraMap k k)), dY.map (mapRingHom (algebraMap k k)), B, hB,
    fun x y h hx => H x y h hx⟩

theorem exists_rep {α : V₁.toAffine.Point →+ V₂.toAffine.Point}
    (hα : α ∈ rationalHomSet k V₁ V₂) (hα0 : α ≠ 0) :
    ∃ (u v a b c : k[X]) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : V₁.toAffine.Nonsingular x y), x ∉ B →
        v.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ ∃ h', α (.some x y h) =
          .some (u.eval x / v.eval x) ((a.eval x + b.eval x * y) / c.eval x) h' := by
  have hα' : IsRationallyRepresented k V₁ V₂ α := hα.resolve_left hα0
  obtain ⟨u, v, B₁, hB₁, H₁⟩ := exists_xrep hα hα0
  obtain ⟨nX, dX, nY, dY, B₂, hB₂, H₂⟩ := exists_rawrep hα'
  obtain ⟨n₀, n₁, hn⟩ := exists_evalEval_eq_linear V₁.toAffine nY
  obtain ⟨d₀, d₁, hd⟩ := exists_evalEval_eq_linear V₁.toAffine dY
  set R : k[X] := X ^ 3 + C V₁.a₂ * X ^ 2 + C V₁.a₄ * X + C V₁.a₆ with hR
  set T : k[X] := C V₁.a₁ * X + C V₁.a₃ with hT
  refine ⟨u, v, n₀ * d₀ - n₀ * d₁ * T - n₁ * d₁ * R, n₁ * d₀ - n₀ * d₁,
    d₀ ^ 2 - d₀ * d₁ * T - d₁ ^ 2 * R, B₁ ∪ B₂, hB₁.union hB₂, fun x y h hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hv, x', y', h', hP, hx'⟩ := H₁ x y h hx.1
  obtain ⟨hdX, hdY, h'', hP'⟩ := H₂ x y h hx.2

  have hn' : V₁.toAffine.Nonsingular x (V₁.toAffine.negY x y) := (Affine.nonsingular_neg _ _).mpr h
  obtain ⟨-, hdY', -⟩ := H₂ x _ hn' hx.2
  have heq : V₁.toAffine.Equation x y := h.left
  rw [Affine.equation_iff] at heq
  have hdy := hd x y h.left
  have hdy' := hd x _ hn'.left
  have hny := hn x y h.left
  have hc : (d₀ ^ 2 - d₀ * d₁ * T - d₁ ^ 2 * R).eval x =
      dY.evalEval x y * dY.evalEval x (V₁.toAffine.negY x y) := by
    rw [hdy, hdy']
    simp only [hR, hT, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X, Affine.negY]
    linear_combination (d₁.eval x) ^ 2 * heq
  have hab : (n₀ * d₀ - n₀ * d₁ * T - n₁ * d₁ * R).eval x + (n₁ * d₀ - n₀ * d₁).eval x * y =
      nY.evalEval x y * dY.evalEval x (V₁.toAffine.negY x y) := by
    rw [hny, hdy']
    simp only [hR, hT, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X, Affine.negY]
    linear_combination (n₁.eval x * d₁.eval x) * heq
  have hc0 : (d₀ ^ 2 - d₀ * d₁ * T - d₁ ^ 2 * R).eval x ≠ 0 := by
    rw [hc]; exact mul_ne_zero hdY hdY'
  refine ⟨hv, hc0, ?_⟩

  have hPP := hP.symm.trans hP'
  simp only [Affine.Point.some.injEq] at hPP
  have hy' : y' = ((n₀ * d₀ - n₀ * d₁ * T - n₁ * d₁ * R).eval x +
      (n₁ * d₀ - n₀ * d₁).eval x * y) / (d₀ ^ 2 - d₀ * d₁ * T - d₁ ^ 2 * R).eval x := by
    rw [hPP.2, hab, hc, mul_div_mul_right _ _ hdY']
  exact exists_some_of_eq hx' hy' hP

end Field

section Val

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem exists_max (S : Finset L) (hS : ∃ e ∈ S, e ≠ 0) :
    ∃ m ∈ S, m ≠ 0 ∧ ∀ e ∈ S, e / m ∈ A := by
  obtain ⟨e₀, he₀, he₀0⟩ := hS
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S (fun e => A.valuation e) ⟨e₀, he₀⟩
  have hm0 : m ≠ 0 := by
    intro h
    have := hmax e₀ he₀
    rw [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact he₀0 this
  refine ⟨m, hm, hm0, fun e he => ?_⟩
  rw [← A.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hmax e he) zero_le'

theorem exists_lift (p : L[X]) (m : L) (h : ∀ n, p.coeff n / m ∈ A) :
    ∃ P : A[X], P.map A.subtype = C m⁻¹ * p := by
  have : C m⁻¹ * p ∈ Polynomial.lifts A.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨p.coeff n / m, h n⟩, ?_⟩
    rw [Polynomial.coeff_C_mul]
    show p.coeff n / m = _
    rw [div_eq_inv_mul]
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts _).mp this
  exact ⟨P, hP⟩

theorem exists_normalize (S : Finset L[X]) (hS : ∃ p ∈ S, p ≠ 0) :
    ∃ m : L, m ≠ 0 ∧ (∀ p ∈ S, ∃ P : A[X], P.map A.subtype = C m⁻¹ * p) ∧
      ∃ p ∈ S, ∀ P : A[X], P.map A.subtype = C m⁻¹ * p → P.map (residue A) ≠ 0 := by
  classical
  set T : Finset L := S.biUnion Polynomial.coeffs with hT_def
  have hT : ∃ e ∈ T, e ≠ 0 := by
    obtain ⟨p, hp, hp0⟩ := hS
    exact ⟨p.leadingCoeff, Finset.mem_biUnion.mpr
      ⟨p, hp, Polynomial.coeff_mem_coeffs (leadingCoeff_ne_zero.mpr hp0)⟩,
      leadingCoeff_ne_zero.mpr hp0⟩
  obtain ⟨m, hmT, hm0, hdiv⟩ := exists_max (A := A) T hT
  have hcoef : ∀ p ∈ S, ∀ n, p.coeff n / m ∈ A := by
    intro p hp n
    by_cases hn : p.coeff n = 0
    · rw [hn, zero_div]; exact A.zero_mem
    · exact hdiv _ (Finset.mem_biUnion.mpr ⟨p, hp, Polynomial.coeff_mem_coeffs hn⟩)
  refine ⟨m, hm0, fun p hp => exists_lift p m (hcoef p hp), ?_⟩
  obtain ⟨p, hp, hpm⟩ := Finset.mem_biUnion.mp hmT
  obtain ⟨n, -, hn⟩ := Polynomial.mem_coeffs_iff.mp hpm
  refine ⟨p, hp, fun P hP h0 => ?_⟩
  have h2 : ((P.coeff n : A) : L) = 1 := by
    have := congr_arg (fun q => coeff q n) hP
    simp only [coeff_map, coeff_C_mul] at this
    rw [← hn, inv_mul_cancel₀ hm0] at this
    exact this
  have h3 : P.coeff n = 1 := Subtype.ext h2
  have h1 : (P.map (residue A)).coeff n = 1 := by rw [coeff_map, h3, map_one]
  rw [h0, coeff_zero] at h1
  exact zero_ne_one h1

theorem exists_normalize₂ (u v : L[X]) (hv : v ≠ 0) :
    ∃ U V : A[X], (∃ m : L, m ≠ 0 ∧ U.map A.subtype = C m⁻¹ * u ∧ V.map A.subtype = C m⁻¹ * v) ∧
      (U.map (residue A) ≠ 0 ∨ V.map (residue A) ≠ 0) := by
  classical
  obtain ⟨m, hm0, hall, p, hp, hne⟩ :=
    exists_normalize (A := A) ({u, v} : Finset L[X]) ⟨v, by simp, hv⟩
  obtain ⟨U, hU⟩ := hall u (by simp)
  obtain ⟨V, hV⟩ := hall v (by simp)
  refine ⟨U, V, ⟨m, hm0, hU, hV⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Or.inl (hne U hU)
  · exact Or.inr (hne V hV)

theorem exists_normalize₃ (a b c : L[X]) (hc : c ≠ 0) :
    ∃ P Q R : A[X], (∃ m : L, m ≠ 0 ∧ P.map A.subtype = C m⁻¹ * a ∧
      Q.map A.subtype = C m⁻¹ * b ∧ R.map A.subtype = C m⁻¹ * c) ∧
      (P.map (residue A) ≠ 0 ∨ Q.map (residue A) ≠ 0 ∨ R.map (residue A) ≠ 0) := by
  classical
  obtain ⟨m, hm0, hall, p, hp, hne⟩ :=
    exists_normalize (A := A) ({a, b, c} : Finset L[X]) ⟨c, by simp, hc⟩
  obtain ⟨P, hP⟩ := hall a (by simp)
  obtain ⟨Q, hQ⟩ := hall b (by simp)
  obtain ⟨R, hR⟩ := hall c (by simp)
  refine ⟨P, Q, R, ⟨m, hm0, hP, hQ, hR⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact Or.inl (hne P hP)
  · exact Or.inr (Or.inl (hne Q hQ))
  · exact Or.inr (Or.inr (hne R hR))

theorem eval_eq_mul_of_map_eq {p : L[X]} {P : A[X]} {m : L} (hm : m ≠ 0)
    (h : P.map A.subtype = C m⁻¹ * p) (x : L) : p.eval x = m * (P.map A.subtype).eval x := by
  rw [h, eval_mul, eval_C, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]

theorem eval_map_subtype (P : A[X]) {x : L} (hx : x ∈ A) :
    (P.map A.subtype).eval x = ((P.eval ⟨x, hx⟩ : A) : L) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_hom A.subtype ⟨x, hx⟩

theorem residue_eval (P : A[X]) (x : A) :
    residue A (P.eval x) = (P.map (residue A)).eval (residue A x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

open Classical in

noncomputable def resFun (A : ValuationSubring L) (b : L) : ResidueField A :=
  if hb : b ∈ A then residue A ⟨b, hb⟩ else 0

theorem resFun_of_mem {b : L} (hb : b ∈ A) : resFun A b = residue A ⟨b, hb⟩ := by
  unfold resFun; rw [dif_pos hb]

variable (E : WeierstrassCurve A)

theorem isElliptic_map_subtype (hΔ : (E.map (residue A)).Δ ≠ 0) : (E.map A.subtype).IsElliptic := by
  have hu : IsUnit E.Δ := (map_residue_Δ_ne_zero_iff E).mp hΔ
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  exact hu.map A.subtype

theorem isElliptic_map_residue (hΔ : (E.map (residue A)).Δ ≠ 0) :
    (E.map (residue A)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  exact isUnit_iff_ne_zero.mpr hΔ

noncomputable def quadY (x : A) : A[X] :=
  X ^ 2 + (C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆))

theorem quadY_lower_degree_lt (x : A) :
    (C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) : A[X]).degree < 2 := by
  have h12 : (1 : WithBot ℕ) < 2 := by exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  have h02 : (0 : WithBot ℕ) < 2 := by exact_mod_cast (by norm_num : (0 : ℕ) < 2)
  exact (Polynomial.degree_sub_le _ _).trans_lt
    (max_lt ((Polynomial.degree_C_mul_X_le _).trans_lt h12) (Polynomial.degree_C_le.trans_lt h02))

theorem quadY_monic (x : A) : (quadY E x).Monic := by
  unfold quadY
  refine (Polynomial.monic_X_pow 2).add_of_left ?_
  rw [Polynomial.degree_X_pow]
  exact quadY_lower_degree_lt E x

theorem quadY_natDegree (x : A) : (quadY E x).natDegree = 2 := by
  have hdeg : (quadY E x).degree = 2 := by
    unfold quadY
    rw [Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    · rfl
    · rw [Polynomial.degree_X_pow]; exact quadY_lower_degree_lt E x
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

theorem equation_iff_quadY (x y : A) :
    (E.map A.subtype).toAffine.Equation (x : L) (y : L) ↔ (quadY E x).eval y = 0 := by
  rw [show (x : L) = A.subtype x from rfl, show (y : L) = A.subtype y from rfl,
    E.toAffine.map_equation A.subtype_injective x y, Affine.equation_iff]
  simp only [quadY, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

theorem residue_equation_iff_quadY (x : A) (yb : ResidueField A) :
    (E.map (residue A)).toAffine.Equation (residue A x) yb ↔
      ((quadY E x).map (residue A)).eval yb = 0 := by
  rw [Affine.equation_iff]
  simp only [quadY, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

variable [IsAlgClosed L]

theorem exists_Y (x : A) : ∃ y : A, (E.map A.subtype).toAffine.Equation (x : L) (y : L) := by
  obtain ⟨y, hy⟩ := ValuationSubring.exists_root_mem_of_monic A (quadY E x) (quadY_monic E x)
    (by rw [quadY_natDegree]; norm_num)
  refine ⟨y, (equation_iff_quadY E x y).mpr ?_⟩
  have h1 : (((quadY E x).eval y : A) : L) = 0 := by
    rw [Polynomial.aeval_def, show algebraMap A L = A.subtype from rfl,
      show (y : L) = A.subtype y from rfl, Polynomial.eval₂_hom] at hy
    exact hy
  exact_mod_cast h1

theorem exists_Y_residue (x : A) {yb : ResidueField A}
    (h : (E.map (residue A)).toAffine.Equation (residue A x) yb) :
    ∃ y : A, (E.map A.subtype).toAffine.Equation (x : L) (y : L) ∧ residue A y = yb := by
  obtain ⟨y, hy, hres⟩ := ValuationSubring.exists_eval_eq_zero_and_residue_eq A (quadY E x)
    (by rw [(quadY_monic E x).leadingCoeff]; exact isUnit_one) yb
    ((residue_equation_iff_quadY E x yb).mp h)
  exact ⟨y, (equation_iff_quadY E x y).mpr hy, hres⟩

variable [DecidableEq L] [DecidableEq (ResidueField A)] {E}

omit [IsAlgClosed L] in
theorem reduceHom_apply (hΔ : (E.map (residue A)).Δ ≠ 0) (P : (E.map A.subtype).toAffine.Point) :
    reduceHom hΔ P = reducePoint hΔ P :=
  rfl

variable (E) in

theorem reduceHom_ne_zero (hΔ : (E.map (residue A)).Δ ≠ 0) : reduceHom hΔ ≠ 0 := by
  haveI := isElliptic_map_subtype E hΔ
  obtain ⟨y, hy⟩ := exists_Y E 0
  have hns : (E.map A.subtype).toAffine.Nonsingular ((0 : A) : L) (y : L) :=
    Affine.equation_iff_nonsingular.mp hy
  intro h0
  have h1 : reduceHom hΔ (.some _ _ hns) = 0 := by rw [h0, AddMonoidHom.zero_apply]
  rw [reduceHom_apply, reducePoint_some_of_mem hΔ hns (SetLike.coe_mem _)] at h1
  exact Affine.Point.some_ne_zero _ h1

variable (E) in

theorem reduceHom_surjective (hΔ : (E.map (residue A)).Δ ≠ 0) :
    Function.Surjective (reduceHom hΔ) := by
  haveI := isElliptic_map_subtype E hΔ
  intro ρ
  rcases ρ with _ | ⟨xb, yb, hb⟩
  · exact ⟨0, map_zero _⟩
  · obtain ⟨x, rfl⟩ := residue_surjective xb
    obtain ⟨y, hy, rfl⟩ := exists_Y_residue E x hb.left
    have hns : (E.map A.subtype).toAffine.Nonsingular (x : L) (y : L) :=
      Affine.equation_iff_nonsingular.mp hy
    refine ⟨.some x y hns, ?_⟩
    rw [reduceHom_apply, reducePoint_some_of_mem hΔ hns x.2]

variable (E) in

def Generic (F : Set (ResidueField A)) (B : Set L) (P : (E.map A.subtype).toAffine.Point) : Prop :=
  ∃ (x y : L) (h : (E.map A.subtype).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B ∧
    ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∉ F

variable (E) in

noncomputable def xres : (E.map A.subtype).toAffine.Point → ResidueField A
  | .zero => 0
  | .some x _ _ => resFun A x

def xbar {κ : Type*} [Field κ] {V : Affine κ} : V.Point → κ
  | .zero => 0
  | .some x _ _ => x

variable (E) in
omit [DecidableEq L] [DecidableEq (ResidueField A)] in

theorem exists_generic_notMem (hΔ : (E.map (residue A)).Δ ≠ 0) {F : Set (ResidueField A)}
    (hF : F.Finite) {B : Set L} (hB : B.Finite) {X : Set (E.map A.subtype).toAffine.Point}
    (hX : X.Finite) :
    ∃ P, Generic E F B P ∧ P ∉ X := by
  haveI := isElliptic_map_subtype E hΔ
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨xb, hxb⟩ :=
    (((hF.union (hB.image (resFun A))).union (hX.image (xres E)))).infinite_compl.nonempty
  simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff] at hxb
  obtain ⟨⟨hxF, hxB⟩, hxX⟩ := hxb
  obtain ⟨x, rfl⟩ := residue_surjective xb
  obtain ⟨y, hy⟩ := exists_Y E x
  have hns : (E.map A.subtype).toAffine.Nonsingular (x : L) (y : L) :=
    Affine.equation_iff_nonsingular.mp hy
  refine ⟨.some x y hns, ⟨x, y, hns, rfl, ?_, x.2, ?_⟩, ?_⟩
  · intro hxb
    exact hxB ⟨x, hxb, by rw [resFun_of_mem x.2]⟩
  · simpa using hxF
  · intro hP
    exact hxX ⟨_, hP, by show resFun A (x : L) = residue A x; rw [resFun_of_mem x.2]⟩

variable (E) in

theorem exists_generic_sub (hΔ : (E.map (residue A)).Δ ≠ 0) {F : Set (ResidueField A)}
    (hF : F.Finite) {B : Set L} (hB : B.Finite) (Q : (E.map A.subtype).toAffine.Point) :
    ∃ P₁ P₂, Generic E F B P₁ ∧ Generic E F B P₂ ∧ Q = P₁ - P₂ := by
  set ρ := reduceHom hΔ Q with hρ

  set Fpts : Set (E.map (residue A)).toAffine.Point :=
    insert 0 {R | ∃ (xb yb : ResidueField A) (h : (E.map (residue A)).toAffine.Nonsingular xb yb),
      R = .some xb yb h ∧ xb ∈ F} with hFpts
  have hFpts_fin : Fpts.Finite := (finite_setOf_X_mem _ hF).insert 0
  set F₂ : Set (ResidueField A) := xbar '' ((fun R => R - ρ) '' Fpts) with hF₂
  have hF₂ : F₂.Finite := (hFpts_fin.image _).image _

  set Bpts : Set (E.map A.subtype).toAffine.Point :=
    {R | ∃ (x y : L) (h : (E.map A.subtype).toAffine.Nonsingular x y), R = .some x y h ∧ x ∈ B}
  have hBpts : Bpts.Finite := finite_setOf_X_mem _ hB
  set X : Set (E.map A.subtype).toAffine.Point := insert (-Q) ((fun R => R - Q) '' Bpts) with hXdef
  have hXfin : X.Finite := (hBpts.image _).insert _
  obtain ⟨P₂, hP₂, hP₂X⟩ := exists_generic_notMem E hΔ (hF.union hF₂) hB hXfin
  obtain ⟨x₂, y₂, h₂, rfl, hx₂B, hx₂A, hx₂F⟩ := hP₂
  simp only [Set.mem_union, not_or] at hx₂F
  refine ⟨Q + .some x₂ y₂ h₂, .some x₂ y₂ h₂, ?_, ⟨x₂, y₂, h₂, rfl, hx₂B, hx₂A, hx₂F.1⟩,
    (add_sub_cancel_right _ _).symm⟩
  simp only [hXdef, Set.mem_insert_iff, Set.mem_image, not_or, not_exists, not_and] at hP₂X
  obtain ⟨hneg, hXB⟩ := hP₂X
  have hred₂ : reduceHom hΔ (.some x₂ y₂ h₂) = .some (residue A ⟨x₂, hx₂A⟩)
      (residue A ⟨y₂, Affine.Y_mem_of_X_mem E h₂.1 hx₂A⟩) (Affine.nonsingular_residue E hΔ h₂.1) :=
    reducePoint_some_of_mem hΔ h₂ hx₂A
  cases hS : Q + .some x₂ y₂ h₂ with
  | zero => exact absurd (eq_neg_of_add_eq_zero_right hS) hneg
  | some x₁ y₁ h₁ =>
    have hred₁ : reduceHom hΔ (.some x₁ y₁ h₁) = ρ + reduceHom hΔ (.some x₂ y₂ h₂) := by
      rw [← hS, map_add]

    have key : reduceHom hΔ (.some x₁ y₁ h₁) ∉ Fpts := by
      intro hmem
      apply hx₂F.2
      refine ⟨reduceHom hΔ (.some x₂ y₂ h₂), ⟨_, hmem, ?_⟩, ?_⟩
      · show reduceHom hΔ (.some x₁ y₁ h₁) - ρ = _
        rw [hred₁]; abel
      · rw [hred₂]; rfl
    have hx₁A : x₁ ∈ A := by
      by_contra hx₁
      apply key
      rw [reduceHom_apply, reducePoint_some_of_notMem hΔ h₁ hx₁]
      exact Set.mem_insert _ _
    refine ⟨x₁, y₁, h₁, rfl, ?_, hx₁A, ?_⟩
    · intro hx₁B
      refine hXB _ ⟨x₁, y₁, h₁, rfl, hx₁B⟩ ?_
      rw [← hS]; abel
    · intro hx₁F
      apply key
      have e := reducePoint_some_of_mem hΔ h₁ hx₁A
      exact Set.mem_insert_of_mem _ ⟨_, _, _, e, hx₁F⟩

end Val

section Main

variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)] {E₁ E₂ : WeierstrassCurve A}

theorem comp_ne_zero (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point}
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0) :
    (reduceHom hΔ₂).comp μ ≠ 0 := by
  haveI := isElliptic_map_subtype E₁ hΔ₁
  haveI := isElliptic_map_subtype E₂ hΔ₂
  intro h
  have hsurj : Function.Surjective μ := WeierstrassCurve.surjective_of_mem_rationalHomSet L hμ hμ0
  apply reduceHom_ne_zero E₂ hΔ₂
  ext P
  obtain ⟨Q, rfl⟩ := hsurj P
  exact DFunLike.congr_fun h Q

structure Datum (E₁ E₂ : WeierstrassCurve A)
    (μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point) where
  (U V P Q R : A[X])
  B : Set L
  hB : B.Finite
  rep : ∀ (x y : L) (h : (E₁.map A.subtype).toAffine.Nonsingular x y), x ∉ B →
    (V.map A.subtype).eval x ≠ 0 ∧ (R.map A.subtype).eval x ≠ 0 ∧
      ∃ h', μ (.some x y h) = .some ((U.map A.subtype).eval x / (V.map A.subtype).eval x)
        (((P.map A.subtype).eval x + (Q.map A.subtype).eval x * y) / (R.map A.subtype).eval x) h'
  hUV : U.map (residue A) ≠ 0 ∨ V.map (residue A) ≠ 0
  hPQR : P.map (residue A) ≠ 0 ∨ Q.map (residue A) ≠ 0 ∨ R.map (residue A) ≠ 0

omit [DecidableEq (ResidueField A)] in

theorem nonempty_datum (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point}
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0) :
    Nonempty (Datum E₁ E₂ μ) := by
  haveI := isElliptic_map_subtype E₁ hΔ₁
  haveI := isElliptic_map_subtype E₂ hΔ₂
  obtain ⟨u, v, a, b, c, B, hB, H⟩ :=
    exists_rep (k := L) (V₁ := E₁.map A.subtype) (V₂ := E₂.map A.subtype) hμ hμ0

  obtain ⟨x₀, hx₀⟩ := hB.infinite_compl.nonempty
  obtain ⟨y₀, h₀⟩ := exists_nonsingular (E₁.map A.subtype).toAffine x₀
  obtain ⟨hv₀, hc₀, -⟩ := H x₀ y₀ h₀ hx₀
  have hv : v ≠ 0 := by rintro rfl; exact hv₀ (eval_zero)
  have hc : c ≠ 0 := by rintro rfl; exact hc₀ (eval_zero)
  obtain ⟨U, V, ⟨m, hm, hU, hV⟩, hUV⟩ := exists_normalize₂ (A := A) u v hv
  obtain ⟨P, Q, R, ⟨m', hm', hP, hQ, hR⟩, hPQR⟩ := exists_normalize₃ (A := A) a b c hc
  refine ⟨⟨U, V, P, Q, R, B, hB, fun x y h hx => ?_, hUV, hPQR⟩⟩
  obtain ⟨hvx, hcx, h', hPt⟩ := H x y h hx
  rw [eval_eq_mul_of_map_eq hm hV] at hvx
  rw [eval_eq_mul_of_map_eq hm' hR] at hcx
  refine ⟨(mul_ne_zero_iff.mp hvx).2, (mul_ne_zero_iff.mp hcx).2, exists_some_of_eq ?_ ?_ hPt⟩
  · rw [eval_eq_mul_of_map_eq hm hU, eval_eq_mul_of_map_eq hm hV, mul_div_mul_left _ _ hm]
  · rw [eval_eq_mul_of_map_eq hm' hP, eval_eq_mul_of_map_eq hm' hQ, eval_eq_mul_of_map_eq hm' hR,
      show m' * eval x (Polynomial.map A.subtype P) + m' * eval x (Polynomial.map A.subtype Q) * y =
        m' * (eval x (Polynomial.map A.subtype P) + eval x (Polynomial.map A.subtype Q) * y) by ring,
      mul_div_mul_left _ _ hm']

namespace Datum

variable {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point}
  (D : Datum E₁ E₂ μ)

omit [IsAlgClosed L] [DecidableEq (ResidueField A)] in

theorem rep_mem {x : A} {y : L} (h : (E₁.map A.subtype).toAffine.Nonsingular (x : L) y)
    (hxB : (x : L) ∉ D.B) :
    ((D.V.eval x : A) : L) ≠ 0 ∧ ((D.R.eval x : A) : L) ≠ 0 ∧
      ∃ h', μ (.some x y h) = .some (((D.U.eval x : A) : L) / (D.V.eval x : A))
        ((((D.P.eval x : A) : L) + (D.Q.eval x : A) * y) / (D.R.eval x : A)) h' := by
  have := D.rep x y h hxB
  simp only [eval_map_subtype _ x.2, Subtype.coe_eta] at this
  exact this

theorem map_residue_V_ne_zero (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0)
    (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0) :
    D.V.map (residue A) ≠ 0 := by
  intro hV0
  have hU0 : D.U.map (residue A) ≠ 0 := D.hUV.resolve_right (not_not_intro hV0)
  set F : Set (ResidueField A) := {xb | (D.U.map (residue A)).IsRoot xb} with hF
  have hFfin : F.Finite := Polynomial.finite_setOf_isRoot hU0

  have hgen : ∀ T, Generic E₁ F D.B T → reduceHom hΔ₂ (μ T) = 0 := by
    rintro _ ⟨x, y, h, rfl, hxB, hxA, hxF⟩
    obtain ⟨hv, -, h', hP⟩ := D.rep_mem (x := ⟨x, hxA⟩) h hxB
    rw [hP, reduceHom_apply]
    apply reducePoint_some_of_notMem
    apply A.div_notMem _ _ hv
    · rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval]
      exact hxF
    · rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval, hV0, eval_zero]
  apply comp_ne_zero hΔ₁ hΔ₂ hμ hμ0
  ext T
  obtain ⟨P₁, P₂, h₁, h₂, rfl⟩ := exists_generic_sub E₁ hΔ₁ hFfin D.hB T
  rw [AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, map_sub, map_sub, hgen _ h₁, hgen _ h₂,
    sub_zero]

theorem map_residue_R_ne_zero (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0)
    (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0) :
    D.R.map (residue A) ≠ 0 := by
  classical
  intro hR0
  haveI := isElliptic_map_subtype E₁ hΔ₁
  haveI := isElliptic_map_residue E₁ hΔ₁
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hV := D.map_residue_V_ne_zero hΔ₁ hΔ₂ hμ hμ0
  have hPQ : D.P.map (residue A) ≠ 0 ∨ D.Q.map (residue A) ≠ 0 := by
    rcases D.hPQR with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hR0 h

  set G : (ResidueField A)[X] :=
    if D.Q.map (residue A) ≠ 0 then D.Q.map (residue A) else D.P.map (residue A) with hG
  have hG0 : G ≠ 0 := by
    rw [hG]; split_ifs with hq
    · exact hq
    · exact hPQ.resolve_right hq
  have hΨ : (E₁.map (residue A)).Ψ₂Sq ≠ 0 := WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic _
  obtain ⟨xb, hxb⟩ := ((((Polynomial.finite_setOf_isRoot hV).union
    (Polynomial.finite_setOf_isRoot hG0)).union (Polynomial.finite_setOf_isRoot hΨ)).union
    (D.hB.image (resFun A))).infinite_compl.nonempty
  simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq] at hxb
  obtain ⟨⟨⟨hxV, hxG⟩, hxΨ⟩, hxB⟩ := hxb
  obtain ⟨x, rfl⟩ := residue_surjective xb
  have hxB' : (x : L) ∉ D.B := fun h => hxB ⟨x, h, by rw [resFun_of_mem x.2]⟩

  have key : ∀ y : A, (E₁.map A.subtype).toAffine.Equation (x : L) (y : L) →
      (D.P.map (residue A)).eval (residue A x) +
        (D.Q.map (residue A)).eval (residue A x) * residue A y ≠ 0 → False := by
    intro y hy hne
    have hns : (E₁.map A.subtype).toAffine.Nonsingular (x : L) (y : L) :=
      Affine.equation_iff_nonsingular.mp hy
    obtain ⟨-, hr, h', hPt⟩ := D.rep_mem hns hxB'

    have hx' : ((D.U.eval x : A) : L) / (D.V.eval x : A) ∈ A := by
      refine A.div_mem_of_mem_of_notMem_nonunits (SetLike.coe_mem _) ?_
      rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval]
      exact hxV
    have hy' := Affine.Y_mem_of_X_mem E₂ h'.left hx'

    refine A.div_notMem ?_ ?_ hr hy'
    · rw [show ((D.P.eval x : A) : L) + (D.Q.eval x : A) * (y : L) =
        ((D.P.eval x + D.Q.eval x * y : A) : L) by simp,
        A.coe_mem_nonunits_iff_residue_eq_zero, map_add, map_mul, residue_eval, residue_eval]
      exact hne
    · rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval, hR0, eval_zero]
  obtain ⟨y, hy⟩ := exists_Y E₁ x
  rcases eq_or_ne ((D.P.map (residue A)).eval (residue A x) +
      (D.Q.map (residue A)).eval (residue A x) * residue A y) 0 with h1 | h1
  swap
  · exact key y hy h1

  have hyA' : E₁.toAffine.Equation x y := (E₁.toAffine.map_equation A.subtype_injective x y).mp hy
  have hyA : (E₁.map A.subtype).toAffine.Equation (x : L) ((E₁.toAffine.negY x y : A) : L) :=
    ((Affine.equation_neg _ _).mpr hyA').map A.subtype
  rcases eq_or_ne ((D.P.map (residue A)).eval (residue A x) +
      (D.Q.map (residue A)).eval (residue A x) * residue A (E₁.toAffine.negY x y)) 0 with h2 | h2
  swap
  · exact key _ hyA h2
  have hres_neg : residue A (E₁.toAffine.negY x y) =
      (E₁.map (residue A)).toAffine.negY (residue A x) (residue A y) :=
    (Affine.map_negY (residue A) x y).symm
  rw [hres_neg] at h2
  have hdiff : (D.Q.map (residue A)).eval (residue A x) *
      (residue A y - (E₁.map (residue A)).toAffine.negY (residue A x) (residue A y)) = 0 := by
    linear_combination h1 - h2
  rcases ne_or_eq (D.Q.map (residue A)) 0 with hQ | hQ
  · have hGQ : G = D.Q.map (residue A) := by rw [hG, if_pos hQ]
    rw [hGQ] at hxG
    have hyy : residue A y - (E₁.map (residue A)).toAffine.negY (residue A x) (residue A y) = 0 :=
      (mul_eq_zero.mp hdiff).resolve_left hxG
    apply hxΨ
    have heq : (E₁.map (residue A)).toAffine.Equation (residue A x) (residue A y) :=
      Affine.equation_residue E₁ hy
    rw [IsRoot.def, ← sub_negY_sq (E₁.map (residue A)).toAffine heq, hyy, zero_pow two_ne_zero]
  · have hGP : G = D.P.map (residue A) := by rw [hG, if_neg (not_not_intro hQ)]
    rw [hGP] at hxG
    apply hxG
    rw [IsRoot.def]
    rw [hQ, eval_zero, zero_mul, add_zero] at h1
    exact h1

omit [IsAlgClosed L] in

theorem reduce_apply (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0) {x y : L}
    (h : (E₁.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) (hxB : x ∉ D.B)
    (hVx : ¬ (D.V.map (residue A)).IsRoot (residue A ⟨x, hx⟩))
    (hRx : ¬ (D.R.map (residue A)).IsRoot (residue A ⟨x, hx⟩)) :
    ∃ h', reduceHom hΔ₂ (μ (.some x y h)) =
      .some ((D.U.map (residue A)).eval (residue A ⟨x, hx⟩) /
          (D.V.map (residue A)).eval (residue A ⟨x, hx⟩))
        (((D.P.map (residue A)).eval (residue A ⟨x, hx⟩) +
          (D.Q.map (residue A)).eval (residue A ⟨x, hx⟩) *
            residue A ⟨y, Affine.Y_mem_of_X_mem E₁ h.1 hx⟩) /
          (D.R.map (residue A)).eval (residue A ⟨x, hx⟩)) h' := by
  set xA : A := ⟨x, hx⟩ with hxA
  obtain ⟨hv, hr, h', hPt⟩ := D.rep_mem (x := xA) h hxB
  have hyA : y ∈ A := Affine.Y_mem_of_X_mem E₁ h.1 hx
  have hVu : ((D.V.eval xA : A) : L) ∉ A.nonunits := by
    rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval]; exact hVx
  have hRu : ((D.R.eval xA : A) : L) ∉ A.nonunits := by
    rw [A.coe_mem_nonunits_iff_residue_eq_zero, residue_eval]; exact hRx

  have hx'A : ((D.U.eval xA : A) : L) / (D.V.eval xA : A) ∈ A :=
    A.div_mem_of_mem_of_notMem_nonunits (SetLike.coe_mem _) hVu
  have hnum : ((D.P.eval xA : A) : L) + (D.Q.eval xA : A) * y =
      ((D.P.eval xA + D.Q.eval xA * ⟨y, hyA⟩ : A) : L) := by
    simp
  have hy'A : (((D.P.eval xA : A) : L) + (D.Q.eval xA : A) * y) / (D.R.eval xA : A) ∈ A := by
    rw [hnum]
    exact A.div_mem_of_mem_of_notMem_nonunits (SetLike.coe_mem _) hRu
  have hresx : residue A ⟨_, hx'A⟩ =
      (D.U.map (residue A)).eval (residue A xA) / (D.V.map (residue A)).eval (residue A xA) := by
    rw [A.residue_div (SetLike.coe_mem _) (SetLike.coe_mem _) hVu, ← residue_eval, ← residue_eval]
  have hresy : residue A ⟨_, hy'A⟩ =
      ((D.P.map (residue A)).eval (residue A xA) +
          (D.Q.map (residue A)).eval (residue A xA) * residue A ⟨y, hyA⟩) /
        (D.R.map (residue A)).eval (residue A xA) := by
    rw [A.residue_eq_div_of_eq_div hy'A (SetLike.coe_mem (D.P.eval xA + D.Q.eval xA * ⟨y, hyA⟩))
      (SetLike.coe_mem _) hRu (by rw [hnum]), ← residue_eval, ← residue_eval, ← residue_eval,
      map_add, map_mul]
  rw [hPt, reduceHom_apply, reducePoint_some_of_mem hΔ₂ h' hx'A]
  exact exists_some_of_eq hresx hresy rfl

theorem reduce_eq_zero_of_reduce_eq_zero (D : Datum E₁ E₂ μ) (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0)
    (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0)
    {T : (E₁.map A.subtype).toAffine.Point} (hT : reduceHom hΔ₁ T = 0) :
    reduceHom hΔ₂ (μ T) = 0 := by
  have hV := D.map_residue_V_ne_zero hΔ₁ hΔ₂ hμ hμ0
  have hR := D.map_residue_R_ne_zero hΔ₁ hΔ₂ hμ hμ0
  obtain ⟨P₁, P₂, ⟨x₁, y₁, h₁, rfl, hx₁B, hx₁A, hx₁F⟩, ⟨x₂, y₂, h₂, rfl, hx₂B, hx₂A, hx₂F⟩, rfl⟩ :=
    exists_generic_sub E₁ hΔ₁ ((Polynomial.finite_setOf_isRoot hV).union
      (Polynomial.finite_setOf_isRoot hR)) D.hB T
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hx₁F hx₂F

  have e : reduceHom hΔ₁ (.some x₁ y₁ h₁) = reduceHom hΔ₁ (.some x₂ y₂ h₂) := by
    rw [map_sub] at hT
    exact sub_eq_zero.mp hT
  rw [reduceHom_apply, reduceHom_apply, reducePoint_some_of_mem hΔ₁ h₁ hx₁A,
    reducePoint_some_of_mem hΔ₁ h₂ hx₂A] at e
  simp only [Affine.Point.some.injEq] at e
  obtain ⟨ex, ey⟩ := e
  obtain ⟨h₁', H₁⟩ := D.reduce_apply hΔ₂ h₁ hx₁A hx₁B hx₁F.1 hx₁F.2
  obtain ⟨h₂', H₂⟩ := D.reduce_apply hΔ₂ h₂ hx₂A hx₂B hx₂F.1 hx₂F.2
  rw [map_sub, map_sub, H₁, H₂, sub_eq_zero]
  exact some_congr (by rw [ex]) (by rw [ex, ey]) _ _

end Datum

theorem exists_reduction (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point}
    (hμ : μ ∈ rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hμ0 : μ ≠ 0) :
    ∃ ν : (E₁.map (residue A)).toAffine.Point →+ (E₂.map (residue A)).toAffine.Point,
      IsRationallyRepresented (ResidueField A) (E₁.map (residue A)) (E₂.map (residue A)) ν ∧
      (reduceHom hΔ₂).comp μ = ν.comp (reduceHom hΔ₁) ∧ ν ≠ 0 := by
  haveI := isElliptic_map_subtype E₁ hΔ₁
  obtain ⟨D⟩ := nonempty_datum hΔ₁ hΔ₂ hμ hμ0
  have hV := D.map_residue_V_ne_zero hΔ₁ hΔ₂ hμ hμ0
  have hR := D.map_residue_R_ne_zero hΔ₁ hΔ₂ hμ hμ0

  have hwd : ∀ T T', reduceHom hΔ₁ T = reduceHom hΔ₁ T' →
      reduceHom hΔ₂ (μ T) = reduceHom hΔ₂ (μ T') := by
    intro T T' hTT
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    apply D.reduce_eq_zero_of_reduce_eq_zero hΔ₁ hΔ₂ hμ hμ0
    rw [map_sub, hTT, sub_self]

  have hsurj := reduceHom_surjective E₁ hΔ₁
  set s := Function.surjInv hsurj with hs
  have hs' : ∀ ρ, reduceHom hΔ₁ (s ρ) = ρ := Function.surjInv_eq hsurj
  let ν : (E₁.map (residue A)).toAffine.Point →+ (E₂.map (residue A)).toAffine.Point :=
    { toFun := fun ρ => reduceHom hΔ₂ (μ (s ρ))
      map_zero' := by
        show reduceHom hΔ₂ (μ (s 0)) = 0
        rw [hwd (s 0) 0 (by rw [hs', map_zero]), map_zero, map_zero]
      map_add' := fun ρ ρ' => by
        show reduceHom hΔ₂ (μ (s (ρ + ρ'))) = reduceHom hΔ₂ (μ (s ρ)) + reduceHom hΔ₂ (μ (s ρ'))
        rw [← map_add, ← map_add]
        exact hwd _ _ (by rw [map_add, hs', hs', hs']) }
  have hν : ∀ T, ν (reduceHom hΔ₁ T) = reduceHom hΔ₂ (μ T) := fun T => by
    show reduceHom hΔ₂ (μ (s (reduceHom hΔ₁ T))) = _
    exact hwd _ _ (hs' _)
  have hcomp : (reduceHom hΔ₂).comp μ = ν.comp (reduceHom hΔ₁) := by
    ext T
    exact (hν T).symm
  refine ⟨ν, ?_, hcomp, ?_⟩
  ·
    refine ⟨C (D.U.map (residue A)), C (D.V.map (residue A)),
      C (D.P.map (residue A)) + C (D.Q.map (residue A)) * Y, C (D.R.map (residue A)),
      {xb | (D.V.map (residue A)).IsRoot xb} ∪ {xb | (D.R.map (residue A)).IsRoot xb} ∪
        resFun A '' D.B,
      ((Polynomial.finite_setOf_isRoot hV).union (Polynomial.finite_setOf_isRoot hR)).union
        (D.hB.image _), fun xb yb hb hxb => ?_⟩
    have hb' : (E₁.map (residue A)).toAffine.Nonsingular xb yb := hb
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hxb
    obtain ⟨⟨hxV, hxR⟩, hxB⟩ := hxb

    obtain ⟨x, rfl⟩ := residue_surjective xb
    obtain ⟨y, hy, rfl⟩ := exists_Y_residue E₁ x hb'.left
    have hxB' : (x : L) ∉ D.B := fun h => hxB ⟨x, h, by rw [resFun_of_mem x.2]⟩
    have hns : (E₁.map A.subtype).toAffine.Nonsingular (x : L) (y : L) :=
      Affine.equation_iff_nonsingular.mp hy
    have hred : reduceHom hΔ₁ (.some x y hns) = .some (residue A x) (residue A y) hb' := by
      rw [reduceHom_apply, reducePoint_some_of_mem hΔ₁ hns x.2]
    obtain ⟨h', H⟩ := D.reduce_apply hΔ₂ hns x.2 hxB' (by simpa using hxV) (by simpa using hxR)
    have hνP := (congr_arg ν hred).symm.trans ((hν _).trans H)
    refine ⟨by rw [evalEvalBC_self, evalEval_C]; exact hxV,
      by rw [evalEvalBC_self, evalEval_C]; exact hxR, ?_⟩
    exact exists_some_of_eq
      (by simp only [evalEvalBC_self, evalEval_C, Subtype.coe_eta])
      (by simp only [evalEvalBC_self, evalEval_C, evalEval_add, evalEval_mul, evalEval_X,
        Subtype.coe_eta])
      hνP
  · intro hν0
    apply comp_ne_zero hΔ₁ hΔ₂ hμ hμ0
    rw [hcomp, hν0, AddMonoidHom.zero_comp]

end Main

end WeierstrassCurve.ReduceRationalHom

open WeierstrassCurve.ReduceRationalHom in
theorem solution {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E₁ E₂ : WeierstrassCurve A) (hΔ₁ : (E₁.map (IsLocalRing.residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (IsLocalRing.residue A)).Δ ≠ 0) {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point} (hμ : μ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) : ∃ ν ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) (E₁.map (IsLocalRing.residue A)) (E₂.map (IsLocalRing.residue A)), (WeierstrassCurve.reduceHom hΔ₂).comp μ = AddMonoidHom.comp ν (WeierstrassCurve.reduceHom hΔ₁) ∧ (μ ≠ 0 → ν ≠ 0) := by
  by_cases hμ0 : μ = 0
  · refine ⟨0, WeierstrassCurve.zero_mem_rationalHomSet _ _ _, ?_, fun h => absurd hμ0 h⟩
    subst hμ0
    rw [AddMonoidHom.comp_zero]
    exact (AddMonoidHom.zero_comp _).symm
  · obtain ⟨ν, hν, hcomp, hν0⟩ := exists_reduction hΔ₁ hΔ₂ hμ hμ0
    exact ⟨ν, Or.inr hν, hcomp, fun _ => hν0⟩

end S_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom (solution)
