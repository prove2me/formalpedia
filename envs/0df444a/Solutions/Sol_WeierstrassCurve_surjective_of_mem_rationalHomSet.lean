-- Prove2me | solution 1 for WeierstrassCurve.surjective_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cf3c60c9-fc97-5402-8b30-c5837868ecc5

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_surjective_of_mem_rationalHomSet

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne a₃ a₁ map a₄ a₂ a₆ Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj toAffine Affine.Point Affine.natDegree_polynomial Affine.nonsingular_neg Affine.monic_polynomial Affine.equation_iff Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet"
namespace RationalSurj
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem bc_eq_evalEval (p : F[X][Y]) (x y : k) :
    bc x y p = (p.map (mapRingHom (algebraMap F k))).evalEval x y := by
  simp [bc]

variable [DecidableEq k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Generic

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
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

omit [DecidableEq k] in

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

omit [DecidableEq k] in
theorem infinite_point [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  choose f hf using exists_nonsingular (k := k) W
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem exists_add_eq_of_finite [IsAlgClosed k] [W.IsElliptic] {S : Set k} (hS : S.Finite)
    (Q : Pt k W) : ∃ R₁ R₂ : Pt k W, Good W S R₁ ∧ Good W S R₂ ∧ R₁ + R₂ = Q := by
  haveI := infinite_point (k := k) W
  have hbad : ({R : Pt k W | ¬ Good W S R} ∪ (fun T => Q - T) '' {T : Pt k W | ¬ Good W S T}).Finite :=
    (finite_not_good W hS).union ((finite_not_good W hS).image _)
  obtain ⟨R, hR⟩ := hbad.exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image, not_or, not_not, not_exists,
    not_and] at hR
  refine ⟨Q - R, R, ?_, hR.1, sub_add_cancel Q R⟩
  by_contra hQR
  exact hR.2 (Q - R) hQR (sub_sub_cancel Q R)

end Generic

variable {W₁ W₂ : WeierstrassCurve F}

def Repr (α : Pt k W₁ →+ Pt k W₂) (nX dX nY dY : F[X][Y]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
    bc x y dX ≠ 0 ∧ bc x y dY ≠ 0 ∧
      ∃ h', α (.some x y h) = .some (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) h'

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

section Norm

variable (W : WeierstrassCurve F)

noncomputable def Nm (A B : k[X]) : k[X] :=
  A ^ 2 - (C (W.baseChange k).a₁ * X + C (W.baseChange k).a₃) * A * B
    - (X ^ 3 + C (W.baseChange k).a₂ * X ^ 2 + C (W.baseChange k).a₄ * X + C (W.baseChange k).a₆)
      * B ^ 2

omit [DecidableEq k] in
theorem eval_Nm {x y : k} (h : (W.baseChange k).toAffine.Equation x y) (A B : k[X]) :
    (A.eval x + B.eval x * y) * (A.eval x + B.eval x * (W.baseChange k).toAffine.negY x y) =
      (Nm (k := k) W A B).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [Nm, Affine.negY, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
  linear_combination (-(B.eval x) ^ 2) * h

omit [DecidableEq k] in

theorem exists_eq_zero_of_eval_Nm [IsAlgClosed k] [W.IsElliptic] {A B : k[X]} {x : k}
    (hx : (Nm (k := k) W A B).eval x = 0) :
    ∃ (y : k) (_ : (W.baseChange k).toAffine.Nonsingular x y), A.eval x + B.eval x * y = 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular (k := k) W x
  have hprod := eval_Nm (k := k) W hy.left A B
  rw [hx] at hprod
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact ⟨y, hy, h0⟩
  · exact ⟨_, (Affine.nonsingular_neg x y).mpr hy, h0⟩

omit [DecidableEq k] in

theorem exists_linear_rep (p : F[X][Y]) :
    ∃ p₀ p₁ : k[X], ∀ x y : k, (W.baseChange k).toAffine.Equation x y →
      bc x y p = p₀.eval x + p₁.eval x * y := by
  set f := (W.baseChange k).toAffine.polynomial with hf
  set q := p.map (mapRingHom (algebraMap F k)) with hq
  have hmonic : f.Monic := WeierstrassCurve.Affine.monic_polynomial
  have hf1 : f ≠ 1 := by
    intro h1
    have := WeierstrassCurve.Affine.natDegree_polynomial (W := (W.baseChange k).toAffine)
    rw [← hf, h1, natDegree_one] at this
    exact absurd this (by norm_num)
  have hdeg : (q %ₘ f).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt q hmonic hf1
    rw [WeierstrassCurve.Affine.natDegree_polynomial] at this
    omega
  refine ⟨(q %ₘ f).coeff 0, (q %ₘ f).coeff 1, fun x y hxy => ?_⟩
  have hE : f.evalEval x y = 0 := hxy
  rw [bc_eq_evalEval, ← hq]
  conv_lhs => rw [← modByMonic_add_div q f, eq_X_add_C_of_natDegree_le_one hdeg]
  rw [evalEval_add, evalEval_mul, hE, zero_mul, add_zero, evalEval_add, evalEval_mul, evalEval_C,
    evalEval_C, evalEval_X]
  ring

end Norm

omit [DecidableEq k] in

theorem finite_setOf_quad {a₀ a₁ a₂ : k} (h : ¬ (a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0)) :
    {u : k | a₀ + a₁ * u + a₂ * u ^ 2 = 0}.Finite := by
  set r : k[X] := C a₀ + C a₁ * X + C a₂ * X ^ 2 with hr
  have hr0 : r ≠ 0 := by
    intro h0
    apply h
    have h0' := fun n => congrArg (fun p : k[X] => p.coeff n) h0
    have e0 := h0' 0
    have e1 := h0' 1
    have e2 := h0' 2
    simp only [hr, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at e0 e1 e2
    norm_num at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  refine (finite_setOf_isRoot hr0).subset ?_
  intro u hu
  simp only [Set.mem_setOf_eq] at hu ⊢
  simp only [IsRoot.def, hr, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  exact hu

omit [DecidableEq k] in

theorem exists_root_notMem [IsAlgClosed k] {Q₀ Q₁ Q₂ : k[X]}
    (hcop : ∀ b : k, ¬ (Q₀.IsRoot b ∧ Q₁.IsRoot b ∧ Q₂.IsRoot b))
    (hnc : ¬ (Q₀.natDegree = 0 ∧ Q₁.natDegree = 0 ∧ Q₂.natDegree = 0))
    {B : Set k} (hB : B.Finite) :
    ∃ S : Set k, S.Finite ∧ ∀ u ∉ S, ∃ x ∉ B, (Q₀ + C u * Q₁ + C (u ^ 2) * Q₂).IsRoot x := by
  set D := max Q₀.natDegree (max Q₁.natDegree Q₂.natDegree) with hD
  have hD0 : D ≠ 0 := by
    intro h0
    apply hnc
    refine ⟨?_, ?_, ?_⟩ <;> omega

  have hlead : ¬ (Q₀.coeff D = 0 ∧ Q₁.coeff D = 0 ∧ Q₂.coeff D = 0) := by
    rintro ⟨h0, h1, h2⟩
    rcases Nat.le_antisymm_iff.mp hD with ⟨-, -⟩
    have hmax : Q₀.natDegree = D ∨ Q₁.natDegree = D ∨ Q₂.natDegree = D := by omega
    rcases hmax with h | h | h
    · by_cases hq : Q₀ = 0
      · apply hD0; rw [← h, hq, natDegree_zero]
      · exact (leadingCoeff_ne_zero.mpr hq) (by rw [leadingCoeff, h]; exact h0)
    · by_cases hq : Q₁ = 0
      · apply hD0; rw [← h, hq, natDegree_zero]
      · exact (leadingCoeff_ne_zero.mpr hq) (by rw [leadingCoeff, h]; exact h1)
    · by_cases hq : Q₂ = 0
      · apply hD0; rw [← h, hq, natDegree_zero]
      · exact (leadingCoeff_ne_zero.mpr hq) (by rw [leadingCoeff, h]; exact h2)
  set S₁ : Set k := {u | Q₀.coeff D + Q₁.coeff D * u + Q₂.coeff D * u ^ 2 = 0} with hS₁
  set S₂ : Set k := ⋃ b ∈ B, {u | Q₀.eval b + Q₁.eval b * u + Q₂.eval b * u ^ 2 = 0} with hS₂
  have hS₁f : S₁.Finite := finite_setOf_quad hlead
  have hS₂f : S₂.Finite := by
    refine hB.biUnion fun b _ => finite_setOf_quad ?_
    exact hcop b
  refine ⟨S₁ ∪ S₂, hS₁f.union hS₂f, fun u hu => ?_⟩
  rw [Set.mem_union, not_or] at hu
  obtain ⟨hu₁, hu₂⟩ := hu
  set L : k[X] := Q₀ + C u * Q₁ + C (u ^ 2) * Q₂ with hL
  have hLdeg : L.natDegree ≤ D := by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · omega
    · exact (natDegree_C_mul_le _ _).trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans (by omega)
  have hLcoeff : L.coeff D = Q₀.coeff D + Q₁.coeff D * u + Q₂.coeff D * u ^ 2 := by
    simp only [hL, coeff_add, coeff_C_mul]; ring
  have hLD : L.natDegree = D := natDegree_eq_of_le_of_coeff_ne_zero hLdeg (by rwa [hLcoeff])
  have hL0 : L ≠ 0 := by
    intro h0; apply hD0; rw [← hLD, h0, natDegree_zero]
  have hdegL : L.degree ≠ 0 := by
    rw [degree_eq_natDegree hL0, hLD]; exact_mod_cast hD0
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root L hdegL
  refine ⟨x, fun hxB => hu₂ ?_, hx⟩
  rw [hS₂, Set.mem_iUnion₂]
  refine ⟨x, hxB, ?_⟩
  have : L.eval x = 0 := hx
  simp only [hL, eval_add, eval_mul, eval_C] at this
  simp only [Set.mem_setOf_eq]
  linear_combination this

omit [DecidableEq k] in

theorem not_common_root_of_gcd [DecidableEq k[X]] {P₀ P₁ P₂ Q₀ Q₁ Q₂ : k[X]}
    (hG0 : EuclideanDomain.gcd P₀ (EuclideanDomain.gcd P₁ P₂) ≠ 0)
    (h₀ : P₀ = EuclideanDomain.gcd P₀ (EuclideanDomain.gcd P₁ P₂) * Q₀)
    (h₁ : P₁ = EuclideanDomain.gcd P₀ (EuclideanDomain.gcd P₁ P₂) * Q₁)
    (h₂ : P₂ = EuclideanDomain.gcd P₀ (EuclideanDomain.gcd P₁ P₂) * Q₂) (b : k) :
    ¬ (Q₀.IsRoot b ∧ Q₁.IsRoot b ∧ Q₂.IsRoot b) := by
  set G := EuclideanDomain.gcd P₀ (EuclideanDomain.gcd P₁ P₂) with hG
  rintro ⟨r₀, r₁, r₂⟩
  rw [← dvd_iff_isRoot] at r₀ r₁ r₂
  have hd : ∀ {P Q : k[X]}, P = G * Q → X - C b ∣ Q → (X - C b) * G ∣ P := by
    rintro P Q rfl hQ
    rw [mul_comm (X - C b) G]
    exact mul_dvd_mul_left G hQ
  have hdvd : (X - C b) * G ∣ G := by
    rw [hG]
    exact EuclideanDomain.dvd_gcd (hd h₀ r₀) (EuclideanDomain.dvd_gcd (hd h₁ r₁) (hd h₂ r₂))
  obtain ⟨t, ht⟩ := hdvd
  have h1 : (X - C b) * t = 1 := by
    have : G * ((X - C b) * t) = G * 1 := by
      rw [mul_one]; conv_rhs => rw [ht]
      ring
    exact mul_left_cancel₀ hG0 this
  have hunit : IsUnit (X - C b) := IsUnit.of_mul_eq_one _ h1
  rw [isUnit_iff_degree_eq_zero, degree_X_sub_C] at hunit
  exact absurd hunit (by decide)

section Pencil

variable (W : WeierstrassCurve F) (n₀ n₁ d₀ d₁ : k[X])

noncomputable def P₁ : k[X] :=
  -(2 * n₀ * d₀) + (C (W.baseChange k).a₁ * X + C (W.baseChange k).a₃) * (n₀ * d₁ + n₁ * d₀)
    + 2 * (X ^ 3 + C (W.baseChange k).a₂ * X ^ 2 + C (W.baseChange k).a₄ * X + C (W.baseChange k).a₆)
      * n₁ * d₁

omit [DecidableEq k] in
theorem Nm_pencil (u : k) :
    Nm (k := k) W (n₀ - C u * d₀) (n₁ - C u * d₁) =
      Nm W n₀ n₁ + C u * P₁ W n₀ n₁ d₀ d₁ + C (u ^ 2) * Nm W d₀ d₁ := by
  rw [C_pow]
  simp only [Nm, P₁]
  ring

omit [DecidableEq k] in

theorem eval_pencil_eq_zero {x y : k} (hE : (W.baseChange k).toAffine.Equation x y) {u : k}
    (hlin : n₀.eval x + n₁.eval x * y = u * (d₀.eval x + d₁.eval x * y)) :
    (Nm W n₀ n₁ + C u * P₁ W n₀ n₁ d₀ d₁ + C (u ^ 2) * Nm W d₀ d₁).eval x = 0 := by
  rw [← Nm_pencil, ← eval_Nm (k := k) W hE]
  have h0 : (n₀ - C u * d₀).eval x + (n₁ - C u * d₁).eval x * y = 0 := by
    simp only [eval_sub, eval_mul, eval_C]
    linear_combination hlin
  rw [h0, zero_mul]

omit [DecidableEq k] in

theorem lin_of_eval_eq_zero {x y : k} {u : k}
    (h0 : (n₀ - C u * d₀).eval x + (n₁ - C u * d₁).eval x * y = 0) :
    n₀.eval x + n₁.eval x * y = u * (d₀.eval x + d₁.eval x * y) := by
  simp only [eval_sub, eval_mul, eval_C] at h0
  linear_combination h0

end Pencil

section Main

variable [IsAlgClosed k] [W₁.IsElliptic]
variable {α : Pt k W₁ →+ Pt k W₂} {nX dX nY dY : F[X][Y]} {B : Set k}
variable {n₀ n₁ d₀ d₁ : k[X]}

theorem not_proportional (hB : B.Finite) (hrep : Repr α nX dX nY dY B)
    (hn : ∀ x y : k, (W₁.baseChange k).toAffine.Equation x y →
      bc x y nX = n₀.eval x + n₁.eval x * y)
    (hd : ∀ x y : k, (W₁.baseChange k).toAffine.Equation x y →
      bc x y dX = d₀.eval x + d₁.eval x * y)
    (G : k[X]) (c₀ c₁ c₂ : k) (h₀ : Nm W₁ n₀ n₁ = C c₀ * G)
    (h₁ : P₁ W₁ n₀ n₁ d₀ d₁ = C c₁ * G) (h₂ : Nm W₁ d₀ d₁ = C c₂ * G) : False := by

  have hP₂ : Nm W₁ d₀ d₁ ≠ 0 := by
    intro hP
    obtain ⟨x, hxB⟩ := hB.exists_notMem
    obtain ⟨y, hy⟩ := exists_nonsingular (k := k) W₁ x
    have hprod := eval_Nm (k := k) W₁ hy.left d₀ d₁
    rw [hP, eval_zero] at hprod
    rcases mul_eq_zero.mp hprod with h0 | h0
    · exact (hrep x y hy hxB).1 (by rw [hd x y hy.left, h0])
    · have hy' := (Affine.nonsingular_neg x y).mpr hy
      exact (hrep x _ hy' hxB).1 (by rw [hd x _ hy'.left, h0])
  have hG0 : G ≠ 0 := by
    rintro rfl; exact hP₂ (by rw [h₂, mul_zero])
  have hc : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) := by
    rintro ⟨-, -, rfl⟩; exact hP₂ (by rw [h₂, map_zero, zero_mul])

  set T : Set k := {u | c₀ + c₁ * u + c₂ * u ^ 2 = 0} with hT
  have hTf : T.Finite := finite_setOf_quad hc
  set RG : Set k := {x | G.IsRoot x} with hRG
  have hRGf : RG.Finite := finite_setOf_isRoot hG0

  have hsub : {P : Pt k W₁ | Good W₁ (B ∪ RG) P} ⊆ α ⁻¹' {Q : Pt k W₂ | ¬ Good W₂ T Q} := by
    rintro P ⟨x, y, h, rfl, hx⟩
    rw [Set.mem_union, not_or] at hx
    obtain ⟨hdX, -, h', hαP⟩ := hrep x y h hx.1
    set u₀ := bc x y nX / bc x y dX with hu₀
    have hlin : n₀.eval x + n₁.eval x * y = u₀ * (d₀.eval x + d₁.eval x * y) := by
      rw [← hn x y h.left, ← hd x y h.left, hu₀, div_mul_cancel₀ _ hdX]
    have hev := eval_pencil_eq_zero (k := k) W₁ n₀ n₁ d₀ d₁ h.left hlin
    rw [h₀, h₁, h₂] at hev
    simp only [eval_add, eval_mul, eval_C] at hev
    have hq : c₀ + c₁ * u₀ + c₂ * u₀ ^ 2 = 0 := by
      have hGx : G.eval x ≠ 0 := hx.2
      have : (c₀ + c₁ * u₀ + c₂ * u₀ ^ 2) * G.eval x = 0 := by linear_combination hev
      exact (mul_eq_zero.mp this).resolve_right hGx
    change ¬ Good W₂ T (α (.some x y h))
    rw [hαP]
    rintro ⟨x', y', h'', hEq, hx'⟩
    have hxu : u₀ = x' := (Affine.Point.some.inj hEq).left
    exact hx' (by rw [← hxu]; exact hq)

  have hker : {P : Pt k W₁ | α P = 0}.Finite :=
    (finite_not_good W₁ hB).subset (ker_subset_not_good hrep)
  have hgood : {P : Pt k W₁ | Good W₁ (B ∪ RG) P}.Finite :=
    (finite_preimage α hker (finite_not_good W₂ hTf)).subset hsub
  have huniv : (Set.univ : Set (Pt k W₁)).Finite := by
    refine ((finite_not_good W₁ (hB.union hRGf)).union hgood).subset ?_
    intro P _
    by_cases hP : Good W₁ (B ∪ RG) P
    · exact Or.inr hP
    · exact Or.inl hP
  haveI := infinite_point (k := k) W₁
  exact Set.infinite_univ huniv

theorem exists_finite_forall_abscissa (hB : B.Finite) (hrep : Repr α nX dX nY dY B) :
    ∃ S : Set k, S.Finite ∧ ∀ u ∉ S, ∃ (x y : k) (_ : (W₁.baseChange k).toAffine.Nonsingular x y),
      x ∉ B ∧ bc x y nX = u * bc x y dX := by
  classical
  obtain ⟨n₀, n₁, hn⟩ := exists_linear_rep (k := k) W₁ nX
  obtain ⟨d₀, d₁, hd⟩ := exists_linear_rep (k := k) W₁ dX
  by_cases hprop : ∃ (G : k[X]) (c₀ c₁ c₂ : k), Nm W₁ n₀ n₁ = C c₀ * G ∧
      P₁ W₁ n₀ n₁ d₀ d₁ = C c₁ * G ∧ Nm W₁ d₀ d₁ = C c₂ * G
  · obtain ⟨G, c₀, c₁, c₂, h₀, h₁, h₂⟩ := hprop
    exact (not_proportional hB hrep hn hd G c₀ c₁ c₂ h₀ h₁ h₂).elim

  set p₀ := Nm W₁ n₀ n₁ with hp₀
  set p₁ := P₁ W₁ n₀ n₁ d₀ d₁ with hp₁
  set p₂ := Nm W₁ d₀ d₁ with hp₂
  set G := EuclideanDomain.gcd p₀ (EuclideanDomain.gcd p₁ p₂) with hG
  have hG0 : G ≠ 0 := by
    intro h0
    rw [hG, EuclideanDomain.gcd_eq_zero_iff, EuclideanDomain.gcd_eq_zero_iff] at h0
    exact hprop ⟨0, 0, 0, 0, by rw [h0.1, mul_zero], by rw [h0.2.1, mul_zero],
      by rw [h0.2.2, mul_zero]⟩
  obtain ⟨Q₀, hQ₀⟩ : G ∣ p₀ := EuclideanDomain.gcd_dvd_left _ _
  obtain ⟨Q₁, hQ₁⟩ : G ∣ p₁ :=
    (EuclideanDomain.gcd_dvd_right _ _).trans (EuclideanDomain.gcd_dvd_left _ _)
  obtain ⟨Q₂, hQ₂⟩ : G ∣ p₂ :=
    (EuclideanDomain.gcd_dvd_right _ _).trans (EuclideanDomain.gcd_dvd_right _ _)
  have hcop : ∀ b : k, ¬ (Q₀.IsRoot b ∧ Q₁.IsRoot b ∧ Q₂.IsRoot b) :=
    not_common_root_of_gcd hG0 hQ₀ hQ₁ hQ₂
  have hnc : ¬ (Q₀.natDegree = 0 ∧ Q₁.natDegree = 0 ∧ Q₂.natDegree = 0) := by
    rintro ⟨e₀, e₁, e₂⟩
    refine hprop ⟨G, Q₀.coeff 0, Q₁.coeff 0, Q₂.coeff 0, ?_, ?_, ?_⟩
    · rw [hQ₀, mul_comm, ← eq_C_of_natDegree_eq_zero e₀]
    · rw [hQ₁, mul_comm, ← eq_C_of_natDegree_eq_zero e₁]
    · rw [hQ₂, mul_comm, ← eq_C_of_natDegree_eq_zero e₂]
  obtain ⟨S, hS, hroot⟩ := exists_root_notMem hcop hnc hB
  refine ⟨S, hS, fun u hu => ?_⟩
  obtain ⟨x, hxB, hx⟩ := hroot u hu
  have hNm : (Nm (k := k) W₁ (n₀ - C u * d₀) (n₁ - C u * d₁)).eval x = 0 := by
    rw [Nm_pencil, ← hp₀, ← hp₁, ← hp₂, hQ₀, hQ₁, hQ₂]
    have : (Q₀ + C u * Q₁ + C (u ^ 2) * Q₂).eval x = 0 := hx
    simp only [eval_add, eval_mul, eval_C] at this ⊢
    linear_combination G.eval x * this
  obtain ⟨y, hy, h0⟩ := exists_eq_zero_of_eval_Nm (k := k) W₁ hNm
  refine ⟨x, y, hy, hxB, ?_⟩
  rw [hn x y hy.left, hd x y hy.left]
  exact lin_of_eval_eq_zero n₀ n₁ d₀ d₁ h0

theorem some_mem_range (hB : B.Finite) (hrep : Repr α nX dX nY dY B) :
    ∃ S : Set k, S.Finite ∧ ∀ (u v : k) (hR : (W₂.baseChange k).toAffine.Nonsingular u v),
      u ∉ S → (Affine.Point.some u v hR : Pt k W₂) ∈ Set.range α := by
  obtain ⟨S, hS, hX⟩ := exists_finite_forall_abscissa hB hrep

  have hval : ∀ u ∉ S, ∃ (P : Pt k W₁) (v : k) (h'' : (W₂.baseChange k).toAffine.Nonsingular u v),
      α P = .some u v h'' := by
    intro u hu
    obtain ⟨x, y, h, hxB, hlin⟩ := hX u hu
    obtain ⟨hdX, -, h', hαP⟩ := hrep x y h hxB
    have hu' : bc x y nX / bc x y dX = u := by
      rw [hlin, mul_div_assoc, div_self hdX, mul_one]
    subst hu'
    exact ⟨_, _, h', hαP⟩
  refine ⟨S, hS, fun u v hR hu => ?_⟩
  obtain ⟨P, v', h'', hP⟩ := hval u hu
  by_cases hv : v = (W₂.baseChange k).toAffine.negY u v'
  · subst hv
    exact ⟨-P, by rw [map_neg, hP, Affine.Point.neg_some]⟩
  · have hvv : v = v' := Affine.Y_eq_of_Y_ne hR.left h''.left rfl hv
    subst hvv
    exact ⟨P, hP⟩

variable [W₂.IsElliptic]

theorem surjective_of_repr (hB : B.Finite) (hrep : Repr α nX dX nY dY B) :
    Function.Surjective α := by
  obtain ⟨S, hS, hrange⟩ := some_mem_range hB hrep
  intro Q
  obtain ⟨R₁, R₂, ⟨u₁, v₁, h₁, rfl, hu₁⟩, ⟨u₂, v₂, h₂, rfl, hu₂⟩, rfl⟩ :=
    exists_add_eq_of_finite (k := k) W₂ hS Q
  obtain ⟨P₁, hP₁⟩ := hrange u₁ v₁ h₁ hu₁
  obtain ⟨P₂, hP₂⟩ := hrange u₂ v₂ h₂ hu₂
  exact ⟨P₁ + P₂, by rw [map_add, hP₁, hP₂]⟩

end Main

end WeierstrassCurve.RationalSurj

open WeierstrassCurve.RationalSurj in

theorem solution {F : Type*} [Field F] (k : Type*)
    [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) :
    Function.Surjective α := by
  rcases hα with h | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · exact absurd h hα0
  · exact surjective_of_repr hB hrep

end S_WeierstrassCurve_surjective_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_surjective_of_mem_rationalHomSet (solution)
