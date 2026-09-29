-- Prove2me | solution 1 for WeierstrassCurve.exists_polynomial_rep_of_injective_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2074418c-1906-504a-8160-f37a01a50387

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.CoordinateRing.smul_basis_eq_zero Affine.slope_of_X_ne Affine.equation_neg a₃ a₁ map Affine.CoordinateRing.norm_smul_basis b₂ Affine.CoordinateRing Affine.CoordinateRing.smul mk a₄ a₂ a₆ Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj toAffine Affine.Point Affine.monic_polynomial b₆ b₈ Δ Affine.equation_iff Affine.polynomial baseChange b₄ rationalHomSet"
namespace RationalHomPolyRep
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing"

section Lin

variable {S : Type*} [CommRing S]

noncomputable def lin (p q : S[X]) : S[X][Y] := C p + C q * Y

theorem evalEval_lin (p q : S[X]) (x y : S) : (lin p q).evalEval x y = p.eval x + q.eval x * y := by
  rw [lin, evalEval_add, evalEval_mul, evalEval_C, evalEval_C, evalEval_X]

theorem C_mul_lin (N p q : S[X]) : C N * lin p q = lin (N * p) (N * q) := by
  simp only [lin, map_mul]; ring

end Lin

section OverK

variable {k : Type*} [Field k]

noncomputable def Nm (E : Affine k) (p q : k[X]) : k[X] :=
  p ^ 2 - p * q * (C E.a₁ * X + C E.a₃) - q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)

noncomputable def conj (E : Affine k) (p q : k[X]) : k[X][Y] :=
  lin (p - q * (C E.a₁ * X + C E.a₃)) (-q)

theorem eq_zero_of_Nm_eq_zero (E : Affine k) {p q : k[X]} (h : Nm E p q = 0) : p = 0 ∧ q = 0 := by
  classical
  have key : Algebra.norm k[X] (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y) = 0 := by
    rw [Affine.CoordinateRing.norm_smul_basis]; exact h
  haveI : Module.Free k[X] E.CoordinateRing := Module.Free.of_basis (CoordinateRing.basis E)
  haveI : Module.Finite k[X] E.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis E)
  rw [Algebra.norm_eq_zero_iff] at key
  exact Affine.CoordinateRing.smul_basis_eq_zero key

theorem smul_basis_ne_zero (E : Affine k) {p q : k[X]} (h : p ≠ 0 ∨ q ≠ 0) :
    p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y ≠ 0 := by
  intro h0
  obtain ⟨hp, hq⟩ := Affine.CoordinateRing.smul_basis_eq_zero h0
  rcases h with h | h
  · exact h hp
  · exact h hq

theorem mk_lin (E : Affine k) (p q : k[X]) :
    CoordinateRing.mk E (lin p q) = p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y := by
  rw [lin, map_add, map_mul, Affine.CoordinateRing.smul, Affine.CoordinateRing.smul, mul_one]

theorem mk_lin_ne_zero (E : Affine k) {p q : k[X]} (h : p ≠ 0 ∨ q ≠ 0) :
    CoordinateRing.mk E (lin p q) ≠ 0 := by
  rw [mk_lin]; exact smul_basis_ne_zero E h

theorem lin_inj (E : Affine k) {p q p' q' : k[X]}
    (h : CoordinateRing.mk E (lin p q) = CoordinateRing.mk E (lin p' q')) : p = p' ∧ q = q' := by
  rw [mk_lin, mk_lin] at h
  have h' : (p - p') • (1 : E.CoordinateRing) + (q - q') • CoordinateRing.mk E Y = 0 := by
    rw [sub_smul, sub_smul]
    calc p • (1 : E.CoordinateRing) - p' • 1 + (q • CoordinateRing.mk E Y - q' • CoordinateRing.mk E Y)
        = (p • (1 : E.CoordinateRing) + q • CoordinateRing.mk E Y)
          - (p' • 1 + q' • CoordinateRing.mk E Y) := by abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨h1, h2⟩ := Affine.CoordinateRing.smul_basis_eq_zero h'
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem lin_mul_conj (E : Affine k) (p q : k[X]) :
    lin p q * conj E p q = C (Nm E p q) - C (q ^ 2) * E.polynomial := by
  rw [Affine.polynomial]
  simp only [lin, conj, Nm, map_sub, map_mul, map_pow, map_add, map_neg]
  ring

theorem mk_polynomial (E : Affine k) : CoordinateRing.mk E E.polynomial = 0 := AdjoinRoot.mk_self

theorem mk_lin_mul_conj (E : Affine k) (p q : k[X]) :
    CoordinateRing.mk E (lin p q) * CoordinateRing.mk E (conj E p q) =
      CoordinateRing.mk E (C (Nm E p q)) := by
  rw [← map_mul, lin_mul_conj, map_sub, map_mul, mk_polynomial, mul_zero, sub_zero]

theorem mk_C (E : Affine k) (N : k[X]) : CoordinateRing.mk E (C N) = CoordinateRing.mk E (lin N 0) := by
  simp [lin]

theorem eval_Nm (E : Affine k) (p q : k[X]) {x y : k} (hxy : E.Equation x y) :
    (Nm E p q).eval x = (p.eval x + q.eval x * y) * (p.eval x + q.eval x * E.negY x y) := by
  rw [Affine.equation_iff] at hxy
  simp only [Nm, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X, Affine.negY]
  linear_combination (q.eval x) ^ 2 * hxy

theorem Nm_eval_eq_zero (E : Affine k) {p q : k[X]} {x y : k} (hxy : E.Equation x y)
    (h0 : p.eval x + q.eval x * y = 0) : (Nm E p q).eval x = 0 := by
  rw [eval_Nm E p q hxy, h0, zero_mul]

theorem exists_nonsingular (E : Affine k) [IsAlgClosed k] [E.IsElliptic] (x : k) :
    ∃ y, E.Nonsingular x y := by
  have hdeg : (E.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [Affine.monic_polynomial.degree_map, Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (E.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

theorem exists_equation (E : Affine k) [IsAlgClosed k] [E.IsElliptic] (x : k) :
    ∃ y, E.Equation x y := by
  obtain ⟨y, hy⟩ := exists_nonsingular E x
  exact ⟨y, hy.left⟩

theorem exists_lin (E : Affine k) (G : k[X][Y]) : ∃ p q : k[X],
    CoordinateRing.mk E G = CoordinateRing.mk E (lin p q) ∧
      ∀ x y, E.Equation x y → G.evalEval x y = p.eval x + q.eval x * y := by
  set r : k[X][Y] := G %ₘ E.polynomial with hr_def
  have hne1 : E.polynomial ≠ 1 := by
    intro h
    have := E.natDegree_polynomial
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  have hr : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt G E.monic_polynomial hne1
    rw [E.natDegree_polynomial] at this
    exact Nat.lt_succ_iff.mp this
  have hGr : r + E.polynomial * (G /ₘ E.polynomial) = G := modByMonic_add_div G E.polynomial
  have hreq : r = C (r.coeff 1) * Y + C (r.coeff 0) := eq_X_add_C_of_natDegree_le_one hr
  have hrlin : r = lin (r.coeff 0) (r.coeff 1) := by rw [lin, add_comm]; exact hreq
  refine ⟨r.coeff 0, r.coeff 1, ?_, fun x y hxy => ?_⟩
  · rw [← hGr, map_add, map_mul, mk_polynomial, zero_mul, add_zero, ← hrlin]
  · have h0 : E.polynomial.evalEval x y = 0 := hxy
    rw [← hGr, evalEval_add, evalEval_mul, h0, zero_mul, add_zero]
    conv_lhs => rw [hrlin]
    rw [evalEval_lin]

theorem evalEval_eq_zero_of_mk_eq_zero (E : Affine k) {G : k[X][Y]} (h : CoordinateRing.mk E G = 0)
    {x y : k} (hxy : E.Equation x y) : G.evalEval x y = 0 := by
  obtain ⟨H, rfl⟩ := AdjoinRoot.mk_eq_zero.mp h
  have h0 : E.polynomial.evalEval x y = 0 := hxy
  rw [evalEval_mul, h0, zero_mul]

theorem evalEval_eq_of_mk_eq (E : Affine k) {G H : k[X][Y]}
    (h : CoordinateRing.mk E G = CoordinateRing.mk E H) {x y : k} (hxy : E.Equation x y) :
    G.evalEval x y = H.evalEval x y := by
  rw [← sub_eq_zero, ← map_sub] at h
  have := evalEval_eq_zero_of_mk_eq_zero E h hxy
  rwa [evalEval_sub, sub_eq_zero] at this

theorem eq_zero_of_eval_eq_zero (E : Affine k) [IsAlgClosed k] [E.IsElliptic] {p q : k[X]}
    {B : Set k} (hB : B.Finite)
    (hf : ∀ x y, E.Nonsingular x y → x ∉ B → p.eval x + q.eval x * y = 0) :
    p = 0 ∧ q = 0 := by
  refine eq_zero_of_Nm_eq_zero E ?_
  by_contra hN
  refine hB.infinite_compl ((Polynomial.finite_setOf_isRoot hN).subset fun x hx => ?_)
  obtain ⟨y, hy⟩ := exists_nonsingular E x
  exact Nm_eval_eq_zero E hy.left (hf x y hy hx)

theorem mk_eq_zero_of_evalEval (E : Affine k) [IsAlgClosed k] [E.IsElliptic] {G : k[X][Y]}
    {B : Set k} (hB : B.Finite) (hG : ∀ x y, E.Nonsingular x y → x ∉ B → G.evalEval x y = 0) :
    CoordinateRing.mk E G = 0 := by
  obtain ⟨p, q, hG', hpq⟩ := exists_lin E G
  obtain ⟨rfl, rfl⟩ := eq_zero_of_eval_eq_zero E hB (p := p) (q := q) (fun x y hxy hx => by
    rw [← hpq x y hxy.left]; exact hG x y hxy hx)
  rw [hG']
  simp [lin]

theorem finite_zeroLocus (E : Affine k) [IsAlgClosed k] [E.IsElliptic] (t : k[X][Y]) {x₀ : k}
    (ht : ∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) :
    {x | ∃ y, E.Equation x y ∧ t.evalEval x y = 0}.Finite := by
  obtain ⟨p, q, -, hpq⟩ := exists_lin E t
  have hN : Nm E p q ≠ 0 := by
    intro h0
    obtain ⟨rfl, rfl⟩ := eq_zero_of_Nm_eq_zero E h0
    obtain ⟨y, hy⟩ := exists_equation E x₀
    exact ht y hy (by rw [hpq x₀ y hy]; simp)
  refine (Polynomial.finite_setOf_isRoot hN).subset ?_
  rintro x ⟨y, hxy, h0⟩
  exact Nm_eval_eq_zero E hxy (by rw [← hpq x y hxy]; exact h0)

theorem dvd_of_rootMultiplicity_le [IsAlgClosed k] {N a : k[X]} (hN : N ≠ 0) (ha : a ≠ 0)
    (h : ∀ x, rootMultiplicity x N ≤ rootMultiplicity x a) : N ∣ a := by
  classical
  have hle : N.roots ≤ a.roots := Multiset.le_iff_count.mpr fun x => by
    rw [count_roots, count_roots]; exact h x
  have h1 : (N.roots.map fun r => X - C r).prod ∣ a :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots ha _).mpr hle
  have h2 : C N.leadingCoeff * (N.roots.map fun r => X - C r).prod = N :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree)
  rw [← h2]
  exact (C_mul_dvd (leadingCoeff_ne_zero.mpr hN)).mpr h1

theorem rootMultiplicity_le_of_mul_eq {N Nt a g : k[X]} {x₀ : k} (hNt : Nt.eval x₀ ≠ 0)
    (ha : a ≠ 0) (h : Nt * a = N * g) : rootMultiplicity x₀ N ≤ rootMultiplicity x₀ a := by
  have hNt0 : Nt ≠ 0 := fun h0 => hNt (by rw [h0, eval_zero])
  have hprod : Nt * a ≠ 0 := mul_ne_zero hNt0 ha
  have hg : g ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hprod h
  have hN : N ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hprod h
  have h1 : rootMultiplicity x₀ (Nt * a) = rootMultiplicity x₀ a := by
    rw [rootMultiplicity_mul hprod, rootMultiplicity_eq_zero (fun hr => hNt hr), zero_add]
  rw [← h1, h, rootMultiplicity_mul (mul_ne_zero hN hg)]
  exact Nat.le_add_right _ _

theorem exists_lin_mul (E : Affine k) [IsAlgClosed k] [E.IsElliptic] {n d : k[X][Y]}
    (hd : CoordinateRing.mk E d ≠ 0)
    (h : ∀ x₀ : k, ∃ s t : k[X][Y], (∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) ∧
      CoordinateRing.mk E (n * t) = CoordinateRing.mk E (d * s)) :
    ∃ p q : k[X], CoordinateRing.mk E n = CoordinateRing.mk E d * CoordinateRing.mk E (lin p q) := by
  obtain ⟨d₀, d₁, hd', -⟩ := exists_lin E d
  obtain ⟨a, b, hab, -⟩ := exists_lin E (n * conj E d₀ d₁)
  have hN : Nm E d₀ d₁ ≠ 0 := by
    intro h0
    obtain ⟨rfl, rfl⟩ := eq_zero_of_Nm_eq_zero E h0
    exact hd (by rw [hd']; simp [lin])
  have hdd : CoordinateRing.mk E d * CoordinateRing.mk E (conj E d₀ d₁) =
      CoordinateRing.mk E (C (Nm E d₀ d₁)) := by rw [hd', mk_lin_mul_conj]

  have key : ∀ x₀ : k, (a ≠ 0 → rootMultiplicity x₀ (Nm E d₀ d₁) ≤ rootMultiplicity x₀ a) ∧
      (b ≠ 0 → rootMultiplicity x₀ (Nm E d₀ d₁) ≤ rootMultiplicity x₀ b) := by
    intro x₀
    obtain ⟨s, t, ht, hnt⟩ := h x₀
    obtain ⟨t₀, t₁, ht', htev⟩ := exists_lin E t
    obtain ⟨g₀, g₁, hg, -⟩ := exists_lin E (s * conj E t₀ t₁)
    have hNt : (Nm E t₀ t₁).eval x₀ ≠ 0 := by
      obtain ⟨y, hy⟩ := exists_equation E x₀
      rw [eval_Nm E t₀ t₁ hy]
      refine mul_ne_zero ?_ ?_
      · rw [← htev x₀ y hy]; exact ht y hy
      · have hy' : E.Equation x₀ (E.negY x₀ y) := (Affine.equation_neg ..).mpr hy
        rw [← htev x₀ _ hy']; exact ht _ hy'
    have hprod : CoordinateRing.mk E (lin (Nm E t₀ t₁ * a) (Nm E t₀ t₁ * b)) =
        CoordinateRing.mk E (lin (Nm E d₀ d₁ * g₀) (Nm E d₀ d₁ * g₁)) := by
      rw [← C_mul_lin, ← C_mul_lin, map_mul, map_mul, ← hab, ← hg, ← mk_lin_mul_conj, ← ht',
        ← hdd, map_mul, map_mul]
      have := congrArg (fun z => z * CoordinateRing.mk E (conj E d₀ d₁) *
        CoordinateRing.mk E (conj E t₀ t₁)) hnt
      simp only [map_mul] at this
      linear_combination this
    obtain ⟨ha', hb'⟩ := lin_inj E hprod
    exact ⟨fun ha => rootMultiplicity_le_of_mul_eq hNt ha ha',
      fun hb => rootMultiplicity_le_of_mul_eq hNt hb hb'⟩
  have hdvd_a : Nm E d₀ d₁ ∣ a := by
    by_cases ha : a = 0
    · rw [ha]; exact dvd_zero _
    · exact dvd_of_rootMultiplicity_le hN ha fun x => (key x).1 ha
  have hdvd_b : Nm E d₀ d₁ ∣ b := by
    by_cases hb : b = 0
    · rw [hb]; exact dvd_zero _
    · exact dvd_of_rootMultiplicity_le hN hb fun x => (key x).2 hb
  obtain ⟨a', ha'⟩ := hdvd_a
  obtain ⟨b', hb'⟩ := hdvd_b
  refine ⟨a', b', ?_⟩
  have hconj : CoordinateRing.mk E (conj E d₀ d₁) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mk_C] at hdd
    exact mk_lin_ne_zero E (Or.inl hN) hdd.symm
  have h1 : CoordinateRing.mk E n * CoordinateRing.mk E (conj E d₀ d₁) =
      CoordinateRing.mk E d * CoordinateRing.mk E (lin a' b') * CoordinateRing.mk E (conj E d₀ d₁) := by
    rw [← map_mul (CoordinateRing.mk E), hab, ha', hb', ← C_mul_lin, map_mul, ← hdd]; ring
  exact mul_right_cancel₀ hconj h1

end OverK

section Repr

variable {k : Type*} [Field k] (E : Affine k)

def IsRepr (x₀ : k) (φ : k → k → k) : Prop :=
  ∃ s t : k[X][Y], (∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) ∧
    ∃ B : Set k, B.Finite ∧ x₀ ∉ B ∧
      ∀ x y, E.Equation x y → x ∉ B → t.evalEval x y ≠ 0 ∧ φ x y * t.evalEval x y = s.evalEval x y

variable {E} {x₀ : k}

theorem isRepr_poly (G : k[X][Y]) : IsRepr E x₀ (fun x y => G.evalEval x y) :=
  ⟨G, 1, fun y _ => by simp, ∅, Set.finite_empty, fun h => h, fun x y _ _ => by simp⟩

theorem isRepr_const (c : k) : IsRepr E x₀ (fun _ _ => c) := by
  simpa using isRepr_poly (E := E) (x₀ := x₀) (C (C c))

theorem isRepr_fst : IsRepr E x₀ (fun x _ => x) := by
  have h := isRepr_poly (E := E) (x₀ := x₀) (C X)
  simp only [evalEval_C, eval_X] at h
  exact h

theorem isRepr_snd : IsRepr E x₀ (fun _ y => y) := by
  simpa using isRepr_poly (E := E) (x₀ := x₀) Y

theorem IsRepr.add {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ) (hψ : IsRepr E x₀ ψ) :
    IsRepr E x₀ (fun x y => φ x y + ψ x y) := by
  obtain ⟨s₁, t₁, ht₁, B₁, hB₁, hx₁, h₁⟩ := hφ
  obtain ⟨s₂, t₂, ht₂, B₂, hB₂, hx₂, h₂⟩ := hψ
  refine ⟨s₁ * t₂ + t₁ * s₂, t₁ * t₂, fun y hy => ?_, B₁ ∪ B₂, hB₁.union hB₂,
    fun h => h.elim hx₁ hx₂, fun x y hxy hx => ?_⟩
  · rw [evalEval_mul]; exact mul_ne_zero (ht₁ y hy) (ht₂ y hy)
  · obtain ⟨h1t, h1e⟩ := h₁ x y hxy (fun h => hx (Or.inl h))
    obtain ⟨h2t, h2e⟩ := h₂ x y hxy (fun h => hx (Or.inr h))
    refine ⟨by rw [evalEval_mul]; exact mul_ne_zero h1t h2t, ?_⟩
    simp only [evalEval_add, evalEval_mul]
    linear_combination t₂.evalEval x y * h1e + t₁.evalEval x y * h2e

theorem IsRepr.mul {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ) (hψ : IsRepr E x₀ ψ) :
    IsRepr E x₀ (fun x y => φ x y * ψ x y) := by
  obtain ⟨s₁, t₁, ht₁, B₁, hB₁, hx₁, h₁⟩ := hφ
  obtain ⟨s₂, t₂, ht₂, B₂, hB₂, hx₂, h₂⟩ := hψ
  refine ⟨s₁ * s₂, t₁ * t₂, fun y hy => ?_, B₁ ∪ B₂, hB₁.union hB₂,
    fun h => h.elim hx₁ hx₂, fun x y hxy hx => ?_⟩
  · rw [evalEval_mul]; exact mul_ne_zero (ht₁ y hy) (ht₂ y hy)
  · obtain ⟨h1t, h1e⟩ := h₁ x y hxy (fun h => hx (Or.inl h))
    obtain ⟨h2t, h2e⟩ := h₂ x y hxy (fun h => hx (Or.inr h))
    refine ⟨by rw [evalEval_mul]; exact mul_ne_zero h1t h2t, ?_⟩
    simp only [evalEval_mul]
    linear_combination (ψ x y * t₂.evalEval x y) * h1e + s₁.evalEval x y * h2e

theorem IsRepr.neg {φ : k → k → k} (hφ : IsRepr E x₀ φ) : IsRepr E x₀ (fun x y => -φ x y) := by
  obtain ⟨s₁, t₁, ht₁, B₁, hB₁, hx₁, h₁⟩ := hφ
  refine ⟨-s₁, t₁, ht₁, B₁, hB₁, hx₁, fun x y hxy hx => ?_⟩
  obtain ⟨h1t, h1e⟩ := h₁ x y hxy hx
  exact ⟨h1t, by rw [evalEval_neg, neg_mul, h1e]⟩

theorem IsRepr.sub {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ) (hψ : IsRepr E x₀ ψ) :
    IsRepr E x₀ (fun x y => φ x y - ψ x y) := by
  simpa only [sub_eq_add_neg] using hφ.add hψ.neg

theorem IsRepr.pow {φ : k → k → k} (hφ : IsRepr E x₀ φ) (n : ℕ) :
    IsRepr E x₀ (fun x y => φ x y ^ n) := by
  induction n with
  | zero => simpa using isRepr_const (E := E) (x₀ := x₀) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hφ

theorem IsRepr.div [IsAlgClosed k] [E.IsElliptic] {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ)
    (hψ : IsRepr E x₀ ψ) (h0 : ∀ y, E.Equation x₀ y → ψ x₀ y ≠ 0) :
    IsRepr E x₀ (fun x y => φ x y / ψ x y) := by
  obtain ⟨s₁, t₁, ht₁, B₁, hB₁, hx₁, h₁⟩ := hφ
  obtain ⟨s₂, t₂, ht₂, B₂, hB₂, hx₂, h₂⟩ := hψ
  have hs₂ : ∀ y, E.Equation x₀ y → s₂.evalEval x₀ y ≠ 0 := fun y hy => by
    obtain ⟨h2t, h2e⟩ := h₂ x₀ y hy hx₂
    rw [← h2e]; exact mul_ne_zero (h0 y hy) h2t
  refine ⟨s₁ * t₂, t₁ * s₂, fun y hy => ?_,
    B₁ ∪ B₂ ∪ {x | ∃ y, E.Equation x y ∧ s₂.evalEval x y = 0},
    (hB₁.union hB₂).union (finite_zeroLocus E s₂ hs₂), ?_, fun x y hxy hx => ?_⟩
  · rw [evalEval_mul]; exact mul_ne_zero (ht₁ y hy) (hs₂ y hy)
  · rintro ((h | h) | ⟨y, hy, h⟩)
    · exact hx₁ h
    · exact hx₂ h
    · exact hs₂ y hy h
  · simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at hx
    obtain ⟨⟨hxB₁, hxB₂⟩, hxs⟩ := hx
    obtain ⟨h1t, h1e⟩ := h₁ x y hxy hxB₁
    obtain ⟨h2t, h2e⟩ := h₂ x y hxy hxB₂
    have hs2xy : s₂.evalEval x y ≠ 0 := hxs y hxy
    have hψ0 : ψ x y ≠ 0 := fun h => hs2xy (by rw [← h2e, h, zero_mul])
    refine ⟨by rw [evalEval_mul]; exact mul_ne_zero h1t hs2xy, ?_⟩
    rw [evalEval_mul, evalEval_mul, ← h2e, ← h1e, div_mul_eq_mul_div, div_eq_iff hψ0]
    ring

theorem IsRepr.congr {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ) {S : Set k} (hS : S.Finite)
    (hxS : x₀ ∉ S) (h : ∀ x y, E.Equation x y → x ∉ S → φ x y = ψ x y) : IsRepr E x₀ ψ := by
  obtain ⟨s₁, t₁, ht₁, B₁, hB₁, hx₁, h₁⟩ := hφ
  refine ⟨s₁, t₁, ht₁, B₁ ∪ S, hB₁.union hS, fun h' => h'.elim hx₁ hxS, fun x y hxy hx => ?_⟩
  obtain ⟨h1t, h1e⟩ := h₁ x y hxy (fun h' => hx (Or.inl h'))
  exact ⟨h1t, by rw [← h x y hxy (fun h' => hx (Or.inr h'))]; exact h1e⟩

theorem IsRepr.eval (p : k[X]) {φ : k → k → k} (hφ : IsRepr E x₀ φ) :
    IsRepr E x₀ (fun x y => p.eval (φ x y)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | monomial n c => simpa only [eval_monomial] using (isRepr_const c).mul (hφ.pow n)

theorem IsRepr.evalEval (G : k[X][Y]) {φ ψ : k → k → k} (hφ : IsRepr E x₀ φ)
    (hψ : IsRepr E x₀ ψ) : IsRepr E x₀ (fun x y => G.evalEval (φ x y) (ψ x y)) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => simpa only [evalEval_add] using hp.add hq
  | monomial n p =>
    simpa only [← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_C, evalEval_pow, evalEval_X]
      using (hφ.eval p).mul (hψ.pow n)

theorem IsRepr.exists_mk_eq [IsAlgClosed k] [E.IsElliptic] {φ : k → k → k} (hφ : IsRepr E x₀ φ)
    {n d : k[X][Y]} {S : Set k} (hS : S.Finite)
    (h : ∀ x y, E.Nonsingular x y → x ∉ S →
      d.evalEval x y ≠ 0 ∧ φ x y = n.evalEval x y / d.evalEval x y) :
    ∃ s t : k[X][Y], (∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) ∧
      CoordinateRing.mk E (n * t) = CoordinateRing.mk E (d * s) := by
  obtain ⟨s, t, ht, B, hB, -, hst⟩ := hφ
  refine ⟨s, t, ht, ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  refine mk_eq_zero_of_evalEval E (hB.union hS) fun x y hxy hx => ?_
  obtain ⟨htxy, hφt⟩ := hst x y hxy.left (fun h' => hx (Or.inl h'))
  obtain ⟨hd, hφnd⟩ := h x y hxy (fun h' => hx (Or.inr h'))
  have hn : n.evalEval x y = φ x y * d.evalEval x y := by rw [hφnd, div_mul_cancel₀ _ hd]
  rw [evalEval_sub, evalEval_mul, evalEval_mul]
  linear_combination t.evalEval x y * hn + d.evalEval x y * hφt

end Repr

section Points

variable {k : Type*} [Field k] [DecidableEq k] (E : Affine k)

def Good (B : Set k) (P : E.Point) : Prop :=
  ∃ (x y : k) (h : E.Nonsingular x y), P = .some x y h ∧ x ∉ B

def absc : E.Point → k
  | .zero => 0
  | .some x _ _ => x

omit [DecidableEq k] in
theorem finite_setOf_equation (x : k) : {y : k | E.Equation x y}.Finite := by
  have hne : (E.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : E.Point | ¬ Good E B P}.Finite := by
  have hfin : (insert (0 : E.Point) (⋃ x ∈ B, ⋃ y ∈ {y : k | E.Equation x y},
      {P : E.Point | ∃ h : E.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation E x) fun y _ => ?_
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

omit [DecidableEq k] in
theorem infinite_point [IsAlgClosed k] [E.IsElliptic] : Infinite E.Point := by
  choose f hf using exists_nonsingular E
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : E.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

omit [DecidableEq k] in
theorem finite_absc_eq (x₀ : k) : {P : E.Point | absc E P = x₀}.Finite := by
  refine (finite_not_good E (Set.finite_singleton x₀)).subset ?_
  rintro P hP ⟨x, y, h, rfl, hx⟩
  exact hx hP

omit [DecidableEq k] in
theorem some_congr {x y x' y' : k} {h : E.Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h', (Point.some x y h : E.Point) = Point.some x' y' h' := by
  subst hx hy; exact ⟨h, rfl⟩

omit [DecidableEq k] in
theorem coeffs_eq_zero_of_eq_zero {m₃ m₂ m₁ m₀ : k}
    (h : C m₃ * X ^ 3 + C m₂ * X ^ 2 + C m₁ * X + C m₀ = (0 : k[X])) :
    m₃ = 0 ∧ m₂ = 0 ∧ m₁ = 0 ∧ m₀ = 0 := by
  have e3 := congrArg (coeff · 3) h
  have e2 := congrArg (coeff · 2) h
  have e1 := congrArg (coeff · 1) h
  have e0 := congrArg (coeff · 0) h
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at e3 e2 e1 e0
  norm_num at e3 e2 e1 e0
  exact ⟨e3, e2, e1, e0⟩

theorem finite_two_torsion [E.IsElliptic] : {T : E.Point | T + T = 0}.Finite := by
  set Ψ : k[X] := C 4 * X ^ 3 + C E.b₂ * X ^ 2 + C (2 * E.b₄) * X + C E.b₆ with hΨdef
  have hΨ : Ψ ≠ 0 := by
    intro h0
    obtain ⟨e3, e2, e1, e0⟩ := coeffs_eq_zero_of_eq_zero h0
    apply E.isUnit_Δ.ne_zero
    rw [WeierstrassCurve.Δ]
    linear_combination (-E.b₂ * E.b₈ + 9 * E.b₄ * E.b₆) * e2 + (-27 * E.b₆) * e0
      + (-2 * E.b₄ ^ 3) * e3
  refine (finite_not_good E (Polynomial.finite_setOf_isRoot hΨ)).subset ?_
  rintro T (hT : T + T = 0) ⟨x, y, h, rfl, hx⟩
  by_cases hy : y = E.negY x y
  · apply hx
    have hE := (Affine.equation_iff x y).mp h.left
    show Ψ.IsRoot x
    simp only [IsRoot.def, hΨdef, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    rw [Affine.negY] at hy
    linear_combination (-4) * hE + (2 * y + E.a₁ * x + E.a₃) * hy
  · rw [Point.add_self_of_Y_ne hy] at hT
    exact Point.some_ne_zero _ hT

theorem finite_setOf_add_self_eq [E.IsElliptic] (R : E.Point) :
    {Q : E.Point | Q + Q = R}.Finite := by
  by_cases hne : {Q : E.Point | Q + Q = R}.Nonempty
  · obtain ⟨Q₁, hQ₁⟩ := hne
    refine ((finite_two_torsion E).preimage (f := fun Q => Q - Q₁)
      fun a _ b _ h => sub_left_injective h).subset ?_
    intro Q hQ
    show (Q - Q₁) + (Q - Q₁) = 0
    have : (Q - Q₁) + (Q - Q₁) = (Q + Q) - (Q₁ + Q₁) := by abel
    rw [this, show Q + Q = R from hQ, show Q₁ + Q₁ = R from hQ₁, sub_self]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

theorem exists_generic [IsAlgClosed k] [E.IsElliptic] (x₀ : k) {BF : Set k} (hBF : BF.Finite) :
    ∃ (xQ yQ : k) (hQ : E.Nonsingular xQ yQ), xQ ≠ x₀ ∧
      ∀ P : E.Point, absc E P = x₀ →
        Good E BF (P + .some xQ yQ hQ) ∧ P + (.some xQ yQ hQ + .some xQ yQ hQ) ≠ 0 := by
  set S : Set E.Point := {Q | ¬ Good E {x₀} Q} ∪
    ⋃ P ∈ {P : E.Point | absc E P = x₀},
      ((fun Q => P + Q) ⁻¹' {R | ¬ Good E BF R} ∪ {Q | Q + Q = -P}) with hSdef
  have hS : S.Finite := by
    refine (finite_not_good E (Set.finite_singleton x₀)).union
      (Set.Finite.biUnion (finite_absc_eq E x₀) fun P _ => Set.Finite.union ?_ ?_)
    · exact (finite_not_good E hBF).preimage fun a _ b _ h => add_right_injective P h
    · exact finite_setOf_add_self_eq E (-P)
  haveI := infinite_point E
  obtain ⟨Q, hQS⟩ := hS.infinite_compl.nonempty
  have hA : Good E {x₀} Q := by
    by_contra h; exact hQS (Or.inl h)
  obtain ⟨xQ, yQ, hQ, rfl, hxQ⟩ := hA
  refine ⟨xQ, yQ, hQ, hxQ, fun P hP => ?_⟩
  have hB : Point.some xQ yQ hQ ∉
      (fun Q => P + Q) ⁻¹' {R | ¬ Good E BF R} ∪ {Q | Q + Q = -P} :=
    fun h => hQS (Or.inr (Set.mem_biUnion (x := P) hP h))
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_not] at hB
  refine ⟨hB.left, fun h => hB.right (eq_neg_of_add_eq_zero_right h)⟩

end Points

section Formula

variable {k : Type*} [Field k]

def slQ (xQ yQ x y : k) : k := (y - yQ) / (x - xQ)

def X3 (E : Affine k) (xQ yQ x y : k) : k := E.addX x xQ (slQ xQ yQ x y)

def Y3 (E : Affine k) (xQ yQ x y : k) : k := E.addY x xQ y (slQ xQ yQ x y)

noncomputable def F3 (E : Affine k) (n d : k[X][Y]) (xQ yQ x y : k) : k :=
  n.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y) / d.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y)

noncomputable def sl2 (E E' : Affine k) (n d n' d' : k[X][Y]) (xQ yQ xQ' yQ' x y : k) : k :=
  (F3 E n' d' xQ yQ x y - E'.negY xQ' yQ') / (F3 E n d xQ yQ x y - xQ')

noncomputable def ΦX (E E' : Affine k) (n d n' d' : k[X][Y]) (xQ yQ xQ' yQ' x y : k) : k :=
  E'.addX (F3 E n d xQ yQ x y) xQ' (sl2 E E' n d n' d' xQ yQ xQ' yQ' x y)

noncomputable def ΦY (E E' : Affine k) (n d n' d' : k[X][Y]) (xQ yQ xQ' yQ' x y : k) : k :=
  E'.addY (F3 E n d xQ yQ x y) xQ' (F3 E n' d' xQ yQ x y) (sl2 E E' n d n' d' xQ yQ xQ' yQ' x y)

variable {E : Affine k} {x₀ : k}

theorem IsRepr.affNegY (E' : Affine k) {φ ψ : k → k → k} (h₁ : IsRepr E x₀ φ)
    (h₂ : IsRepr E x₀ ψ) : IsRepr E x₀ (fun x y => E'.negY (φ x y) (ψ x y)) :=
  (h₂.neg.sub ((isRepr_const _).mul h₁)).sub (isRepr_const _)

theorem IsRepr.affAddX (E' : Affine k) {φ ψ L : k → k → k} (h₁ : IsRepr E x₀ φ)
    (h₂ : IsRepr E x₀ ψ) (hL : IsRepr E x₀ L) :
    IsRepr E x₀ (fun x y => E'.addX (φ x y) (ψ x y) (L x y)) :=
  ((((hL.pow 2).add ((isRepr_const _).mul hL)).sub (isRepr_const _)).sub h₁).sub h₂

theorem IsRepr.affNegAddY (E' : Affine k) {φ ψ χ L : k → k → k} (h₁ : IsRepr E x₀ φ)
    (h₂ : IsRepr E x₀ ψ) (h₃ : IsRepr E x₀ χ) (hL : IsRepr E x₀ L) :
    IsRepr E x₀ (fun x y => E'.negAddY (φ x y) (ψ x y) (χ x y) (L x y)) :=
  (hL.mul ((h₁.affAddX E' h₂ hL).sub h₁)).add h₃

theorem IsRepr.affAddY (E' : Affine k) {φ ψ χ L : k → k → k} (h₁ : IsRepr E x₀ φ)
    (h₂ : IsRepr E x₀ ψ) (h₃ : IsRepr E x₀ χ) (hL : IsRepr E x₀ L) :
    IsRepr E x₀ (fun x y => E'.addY (φ x y) (ψ x y) (χ x y) (L x y)) :=
  (h₁.affAddX E' h₂ hL).affNegY E' (h₁.affNegAddY E' h₂ h₃ hL)

end Formula

section Main

variable {k : Type*} [Field k] [DecidableEq k] {E E' : Affine k}

theorem pointwise (u : E.Point →+ E'.Point) (hinj : Function.Injective u)
    {n d n' d' : k[X][Y]} {BF : Set k}
    (hrep : ∀ x y (h : E.Nonsingular x y), x ∉ BF → d.evalEval x y ≠ 0 ∧ d'.evalEval x y ≠ 0 ∧
      ∃ h', u (.some x y h) =
        .some (n.evalEval x y / d.evalEval x y) (n'.evalEval x y / d'.evalEval x y) h')
    {xQ yQ : k} {hQ : E.Nonsingular xQ yQ} {xQ' yQ' : k} {hQ' : E'.Nonsingular xQ' yQ'}
    (huQ : u (.some xQ yQ hQ) = .some xQ' yQ' hQ')
    {x y : k} (h : E.Nonsingular x y) (hx : x ≠ xQ)
    (hgood : Good E BF (Point.some x y h + Point.some xQ yQ hQ))
    (h2 : Point.some x y h + (Point.some xQ yQ hQ + Point.some xQ yQ hQ) ≠ 0) :
    d.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y) ≠ 0 ∧
      d'.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y) ≠ 0 ∧
      F3 E n d xQ yQ x y ≠ xQ' ∧
      ∃ h'', u (.some x y h) =
        .some (ΦX E E' n d n' d' xQ yQ xQ' yQ' x y) (ΦY E E' n d n' d' xQ yQ xQ' yQ' x y) h'' := by
  obtain ⟨h₃, hPQ⟩ : ∃ h₃, Point.some x y h + Point.some xQ yQ hQ =
      Point.some (X3 E xQ yQ x y) (Y3 E xQ yQ x y) h₃ := by
    rw [Point.add_of_X_ne hx]
    exact some_congr E (by rw [X3, slQ, Affine.slope_of_X_ne hx])
      (by rw [Y3, slQ, Affine.slope_of_X_ne hx])
  obtain ⟨x₃, y₃, h₃', h3eq, hx₃⟩ := hgood
  rw [hPQ] at h3eq
  obtain ⟨rfl, rfl⟩ := Point.some.inj h3eq
  obtain ⟨hd, hd', h₃'', hu3⟩ := hrep _ _ h₃ hx₃
  have hF : n.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y) /
      d.evalEval (X3 E xQ yQ x y) (Y3 E xQ yQ x y) ≠ xQ' := by
    intro hF
    rcases (Point.X_eq_iff (h₁ := h₃'') (h₂ := hQ')).mp hF with heq | heq
    · rw [← hu3, ← huQ] at heq
      have hP := hinj heq
      rw [← hPQ] at hP
      exact Point.some_ne_zero h (add_right_cancel (b := Point.some xQ yQ hQ)
        (hP.trans (zero_add _).symm))
    · rw [← hu3, ← huQ, ← map_neg] at heq
      have hP := hinj heq
      rw [← hPQ] at hP
      exact h2 (by rw [← add_assoc, hP, neg_add_cancel])
  refine ⟨hd, hd', hF, ?_⟩
  have huP : u (Point.some x y h) =
      u (Point.some x y h + Point.some xQ yQ hQ) + u (-Point.some xQ yQ hQ) := by
    rw [← map_add, add_neg_cancel_right]
  rw [hPQ, hu3, map_neg, huQ, Point.neg_some, Point.add_of_X_ne hF] at huP
  obtain ⟨h'', he⟩ := some_congr E' (h := nonsingular_add h₃'' ((nonsingular_neg ..).mpr hQ')
      fun hxy => hF hxy.left)
    (x' := ΦX E E' n d n' d' xQ yQ xQ' yQ' x y) (y' := ΦY E E' n d n' d' xQ yQ xQ' yQ' x y)
    (by rw [Affine.slope_of_X_ne hF]; rfl) (by rw [Affine.slope_of_X_ne hF]; rfl)
  exact ⟨h'', huP.trans he⟩

theorem isRepr_Φ [IsAlgClosed k] [E.IsElliptic] (u : E.Point →+ E'.Point)
    (hinj : Function.Injective u) {n d n' d' : k[X][Y]} {BF : Set k}
    (hrep : ∀ x y (h : E.Nonsingular x y), x ∉ BF → d.evalEval x y ≠ 0 ∧ d'.evalEval x y ≠ 0 ∧
      ∃ h', u (.some x y h) =
        .some (n.evalEval x y / d.evalEval x y) (n'.evalEval x y / d'.evalEval x y) h')
    {xQ yQ : k} {hQ : E.Nonsingular xQ yQ} {xQ' yQ' : k} {hQ' : E'.Nonsingular xQ' yQ'}
    (huQ : u (.some xQ yQ hQ) = .some xQ' yQ' hQ') {x₀ : k} (hxQ : xQ ≠ x₀)
    (hgen : ∀ P : E.Point, absc E P = x₀ →
      Good E BF (P + .some xQ yQ hQ) ∧ P + (.some xQ yQ hQ + .some xQ yQ hQ) ≠ 0) :
    IsRepr E x₀ (ΦX E E' n d n' d' xQ yQ xQ' yQ') ∧
      IsRepr E x₀ (ΦY E E' n d n' d' xQ yQ xQ' yQ') := by
  have hpw : ∀ y, E.Equation x₀ y →
      d.evalEval (X3 E xQ yQ x₀ y) (Y3 E xQ yQ x₀ y) ≠ 0 ∧
        d'.evalEval (X3 E xQ yQ x₀ y) (Y3 E xQ yQ x₀ y) ≠ 0 ∧ F3 E n d xQ yQ x₀ y ≠ xQ' := by
    intro y hy
    have h : E.Nonsingular x₀ y := (equation_iff_nonsingular).mp hy
    obtain ⟨hg, h2⟩ := hgen (Point.some x₀ y h) rfl
    obtain ⟨hd, hd', hF, -⟩ := pointwise u hinj hrep huQ h hxQ.symm hg h2
    exact ⟨hd, hd', hF⟩
  have hsl : IsRepr E x₀ (slQ xQ yQ) :=
    (isRepr_snd.sub (isRepr_const yQ)).div (isRepr_fst.sub (isRepr_const xQ))
      fun y _ => sub_ne_zero.mpr hxQ.symm
  have hX3 : IsRepr E x₀ (X3 E xQ yQ) := isRepr_fst.affAddX E (isRepr_const xQ) hsl
  have hY3 : IsRepr E x₀ (Y3 E xQ yQ) := isRepr_fst.affAddY E (isRepr_const xQ) isRepr_snd hsl
  have hF3 : IsRepr E x₀ (F3 E n d xQ yQ) :=
    (IsRepr.evalEval n hX3 hY3).div (IsRepr.evalEval d hX3 hY3) fun y hy => (hpw y hy).1
  have hG3 : IsRepr E x₀ (F3 E n' d' xQ yQ) :=
    (IsRepr.evalEval n' hX3 hY3).div (IsRepr.evalEval d' hX3 hY3) fun y hy => (hpw y hy).2.1
  have hsl2 : IsRepr E x₀ (sl2 E E' n d n' d' xQ yQ xQ' yQ') :=
    (hG3.sub (isRepr_const _)).div (hF3.sub (isRepr_const xQ'))
      fun y hy => sub_ne_zero.mpr (hpw y hy).2.2
  exact ⟨hF3.affAddX E' (isRepr_const xQ') hsl2, hF3.affAddY E' (isRepr_const xQ') hG3 hsl2⟩

theorem main [IsAlgClosed k] [E.IsElliptic] (u : E.Point →+ E'.Point)
    (hinj : Function.Injective u) {n d n' d' : k[X][Y]} {BF : Set k} (hBF : BF.Finite)
    (hrep : ∀ x y (h : E.Nonsingular x y), x ∉ BF → d.evalEval x y ≠ 0 ∧ d'.evalEval x y ≠ 0 ∧
      ∃ h', u (.some x y h) =
        .some (n.evalEval x y / d.evalEval x y) (n'.evalEval x y / d'.evalEval x y) h') :
    ∃ pX qX pY qY : k[X], ∀ x y, E.Nonsingular x y → x ∉ BF →
      n.evalEval x y / d.evalEval x y = pX.eval x + qX.eval x * y ∧
        n'.evalEval x y / d'.evalEval x y = pY.eval x + qY.eval x * y := by
  obtain ⟨xg, hxg⟩ := hBF.infinite_compl.nonempty
  obtain ⟨yg, hg⟩ := exists_nonsingular E xg
  obtain ⟨hdg, hdg', -⟩ := hrep xg yg hg hxg
  have hd : CoordinateRing.mk E d ≠ 0 := fun h0 =>
    hdg (evalEval_eq_zero_of_mk_eq_zero E h0 hg.left)
  have hd' : CoordinateRing.mk E d' ≠ 0 := fun h0 =>
    hdg' (evalEval_eq_zero_of_mk_eq_zero E h0 hg.left)
  have key : ∀ x₀ : k,
      (∃ s t : k[X][Y], (∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) ∧
        CoordinateRing.mk E (n * t) = CoordinateRing.mk E (d * s)) ∧
      (∃ s t : k[X][Y], (∀ y, E.Equation x₀ y → t.evalEval x₀ y ≠ 0) ∧
        CoordinateRing.mk E (n' * t) = CoordinateRing.mk E (d' * s)) := by
    intro x₀
    obtain ⟨xQ, yQ, hQ, hxQ, hgen⟩ := exists_generic E x₀ hBF
    have hne : u (Point.some xQ yQ hQ) ≠ 0 := fun h0 =>
      Point.some_ne_zero hQ (hinj (h0.trans (map_zero u).symm))
    obtain ⟨xQ', yQ', hQ', huQ⟩ : ∃ (xQ' yQ' : k) (hQ' : E'.Nonsingular xQ' yQ'),
        u (Point.some xQ yQ hQ) = Point.some xQ' yQ' hQ' := by
      generalize u (Point.some xQ yQ hQ) = R at hne ⊢
      cases R with
      | zero => exact (hne Point.zero_def.symm).elim
      | some x' y' h' => exact ⟨x', y', h', rfl⟩
    obtain ⟨hΦX, hΦY⟩ := isRepr_Φ u hinj hrep huQ hxQ hgen
    set Q : E.Point := Point.some xQ yQ hQ with hQdef
    have hT : (({xQ} : Set k) ∪ absc E ''
        ((fun P => P + Q) ⁻¹' {R | ¬ Good E BF R} ∪ {P | P + (Q + Q) = 0})).Finite := by
      refine (Set.finite_singleton _).union (Set.Finite.image _ (Set.Finite.union ?_ ?_))
      · exact (finite_not_good E hBF).preimage fun a _ b _ hab => add_left_injective Q hab
      · exact (Set.finite_singleton (-(Q + Q))).subset fun P hP => eq_neg_of_add_eq_zero_left hP
    have hagree : ∀ x y, E.Nonsingular x y → x ∉ BF ∪ (({xQ} : Set k) ∪ absc E ''
        ((fun P => P + Q) ⁻¹' {R | ¬ Good E BF R} ∪ {P | P + (Q + Q) = 0})) →
        (d.evalEval x y ≠ 0 ∧
          ΦX E E' n d n' d' xQ yQ xQ' yQ' x y = n.evalEval x y / d.evalEval x y) ∧
        (d'.evalEval x y ≠ 0 ∧
          ΦY E E' n d n' d' xQ yQ xQ' yQ' x y = n'.evalEval x y / d'.evalEval x y) := by
      intro x y h hx
      have hxBF : x ∉ BF := fun h' => hx (Or.inl h')
      have hxQ' : x ≠ xQ := fun h' => hx (Or.inr (Or.inl h'))
      have hgoodP : Good E BF (Point.some x y h + Q) := by
        by_contra hng
        exact hx (Or.inr (Or.inr ⟨Point.some x y h, Or.inl hng, rfl⟩))
      have h2P : Point.some x y h + (Q + Q) ≠ 0 := fun h2 =>
        hx (Or.inr (Or.inr ⟨Point.some x y h, Or.inr h2, rfl⟩))
      obtain ⟨-, -, -, h'', huP⟩ := pointwise u hinj hrep huQ h hxQ' hgoodP h2P
      obtain ⟨hdx, hdx', h', huP'⟩ := hrep x y h hxBF
      rw [huP'] at huP
      obtain ⟨hX, hY⟩ := Point.some.inj huP
      exact ⟨⟨hdx, hX.symm⟩, ⟨hdx', hY.symm⟩⟩
    exact ⟨hΦX.exists_mk_eq (hBF.union hT) fun x y h hx => (hagree x y h hx).1,
      hΦY.exists_mk_eq (hBF.union hT) fun x y h hx => (hagree x y h hx).2⟩
  obtain ⟨pX, qX, hX⟩ := exists_lin_mul E hd fun x₀ => (key x₀).1
  obtain ⟨pY, qY, hY⟩ := exists_lin_mul E hd' fun x₀ => (key x₀).2
  refine ⟨pX, qX, pY, qY, fun x y h hx => ?_⟩
  obtain ⟨hdx, hdx', -⟩ := hrep x y h hx
  rw [← map_mul] at hX hY
  have eX := evalEval_eq_of_mk_eq E hX h.left
  have eY := evalEval_eq_of_mk_eq E hY h.left
  rw [evalEval_mul, evalEval_lin] at eX eY
  exact ⟨by rw [eX, mul_div_cancel_left₀ _ hdx], by rw [eY, mul_div_cancel_left₀ _ hdx']⟩

end Main

end WeierstrassCurve.RationalHomPolyRep

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.RationalHomPolyRep in

theorem solution
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point)
    (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (hinj : Function.Injective u) :
    ∃ (pX qX pY qY : Polynomial k) (B : Set k), B.Finite ∧
      ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', u (.some x y h) =
          .some (pX.eval x + qX.eval x * y) (pY.eval x + qY.eval x * y) h' := by
  haveI : (W.baseChange k).IsElliptic := (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  rcases hu with hu0 | ⟨nX, dX, nY, dY, B, hB, hrepF⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_nonsingular (W.baseChange k).toAffine 0
    refine Point.some_ne_zero hy (hinj ?_)
    rw [hu0, map_zero, AddMonoidHom.zero_apply]
  · have hrep : ∀ x y (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        (dX.map (mapRingHom (algebraMap F k))).evalEval x y ≠ 0 ∧
        (dY.map (mapRingHom (algebraMap F k))).evalEval x y ≠ 0 ∧
        ∃ h', u (.some x y h) = .some
          ((nX.map (mapRingHom (algebraMap F k))).evalEval x y /
            (dX.map (mapRingHom (algebraMap F k))).evalEval x y)
          ((nY.map (mapRingHom (algebraMap F k))).evalEval x y /
            (dY.map (mapRingHom (algebraMap F k))).evalEval x y) h' := hrepF
    obtain ⟨pX, qX, pY, qY, hmain⟩ := main u hinj hB hrep
    refine ⟨pX, qX, pY, qY, B, hB, fun x y h hx => ?_⟩
    obtain ⟨-, -, h', hu'⟩ := hrep x y h hx
    obtain ⟨eX, eY⟩ := hmain x y h hx
    obtain ⟨h'', he⟩ := some_congr (W'.baseChange k).toAffine (h := h') eX eY
    exact ⟨h'', hu'.trans he⟩

end S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_polynomial_rep_of_injective_of_mem_rationalHomSet (solution)
