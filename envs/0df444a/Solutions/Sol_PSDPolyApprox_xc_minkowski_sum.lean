-- Prove2me | solution 1 for PSDPolyApprox.xc_minkowski_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:05:50.576527+00:00
-- url     : https://prove2.me/submissions/2cec9a69-d883-4b4a-b5b2-a7aee6dd729a

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity

open ExtensionComplexity.TSP
open scoped Pointwise

namespace Aux_PSDPolyApprox_xc_minkowski_sum

open Matrix

lemma mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) (i : m) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

lemma comp_eq_iff {E F : Type*} (e : F ≃ E) (u v w : E → ℝ) :
    u ∘ e + v ∘ e = w ∘ e ↔ u + v = w := by
  constructor
  · intro h
    funext i
    have := congrFun h (e.symm i)
    simpa using this
  · intro h
    rw [← h]
    rfl

lemma comp_le_iff {E F : Type*} (e : F ≃ E) (u v w : E → ℝ) :
    u ∘ e + v ∘ e ≤ w ∘ e ↔ u + v ≤ w := by
  constructor
  · intro h
    refine Pi.le_def.mpr fun i => ?_
    have := Pi.le_def.mp h (e.symm i)
    simpa using this
  · intro h
    refine Pi.le_def.mpr fun i => ?_
    have := Pi.le_def.mp h (e i)
    simpa using this

lemma toEF {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) {K E R : Type*} [Fintype K] [Fintype E]
    [Fintype R] (r : ℕ) (eR : R ≃ Fin r)
    (A : Matrix E ι ℝ) (B : Matrix E K ℝ) (a : E → ℝ) (C : Matrix R ι ℝ) (D : Matrix R K ℝ)
    (d : R → ℝ)
    (hP : ∀ x, x ∈ P ↔ ∃ y : K → ℝ, A *ᵥ x + B *ᵥ y = a ∧ C *ᵥ x + D *ᵥ y ≤ d) :
    IsEFOfSize P r := by
  classical
  let eK := Fintype.equivFin K
  let eE := Fintype.equivFin E
  refine ⟨Fintype.card K, Fintype.card E, A.submatrix eE.symm (Equiv.refl ι),
    B.submatrix eE.symm eK.symm, a ∘ eE.symm, C.submatrix eR.symm (Equiv.refl ι),
    D.submatrix eR.symm eK.symm, d ∘ eR.symm, ?_⟩
  intro x
  have key : ∀ y' : Fin (Fintype.card K) → ℝ,
      (A.submatrix eE.symm (Equiv.refl ι) *ᵥ x + B.submatrix eE.symm eK.symm *ᵥ y' = a ∘ eE.symm ↔
        A *ᵥ x + B *ᵥ (y' ∘ eK) = a) ∧
      (C.submatrix eR.symm (Equiv.refl ι) *ᵥ x + D.submatrix eR.symm eK.symm *ᵥ y' ≤ d ∘ eR.symm ↔
        C *ᵥ x + D *ᵥ (y' ∘ eK) ≤ d) := by
    intro y'
    simp only [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id]
    exact ⟨comp_eq_iff eE.symm _ _ _, comp_le_iff eR.symm _ _ _⟩
  rw [hP x]
  constructor
  · rintro ⟨y, h1, h2⟩
    have hy : (y ∘ eK.symm) ∘ eK = y := by funext i; simp
    refine ⟨y ∘ eK.symm, ?_, ?_⟩
    · rw [(key _).1, hy]; exact h1
    · rw [(key _).2, hy]; exact h2
  · rintro ⟨y', h1, h2⟩
    exact ⟨y' ∘ eK, (key y').1.mp h1, (key y').2.mp h2⟩

/-! ### Extended formulation of a polytope -/

def polyA (ι : Type*) [DecidableEq ι] : Matrix (Option ι) ι ℝ :=
  Matrix.of fun o j => Option.elim o 0 (fun i => if i = j then 1 else 0)

def polyB {ι : Type*} (V : Finset (ι → ℝ)) : Matrix (Option ι) V ℝ :=
  Matrix.of fun o v => Option.elim o 1 (fun i => -((v : ι → ℝ) i))

def polya (ι : Type*) : Option ι → ℝ := fun o => Option.elim o 1 (fun _ => 0)

lemma polyEF {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (h : IsPolytope P) :
    ∃ r, IsEFOfSize P r := by
  classical
  obtain ⟨V, rfl⟩ := h
  refine ⟨Fintype.card V, toEF _ (Fintype.card V) (Fintype.equivFin V) (polyA ι) (polyB V)
    (polya ι) (0 : Matrix V ι ℝ) (-1 : Matrix V V ℝ) 0 ?_⟩
  intro x
  have hull : x ∈ convexHull ℝ (V : Set (ι → ℝ)) ↔ ∃ y : V → ℝ, (∀ v, 0 ≤ y v) ∧
      ∑ v, y v = 1 ∧ ∀ i, ∑ v, y v * (v : ι → ℝ) i = x i := by
    constructor
    · intro hx
      obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
      refine ⟨fun v => w v, fun v => hw0 v v.2, ?_, ?_⟩
      · rw [Finset.sum_coe_sort V w]; exact hw1
      · intro i
        rw [← hwx, Finset.sum_apply, ← Finset.sum_coe_sort V]
        simp only [Pi.smul_apply, smul_eq_mul]
    · rintro ⟨y, hy0, hy1, hyx⟩
      have hx : ∑ v, y v • (v : ι → ℝ) = x := by
        funext i
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hyx i
      exact mem_convexHull_of_exists_fintype y (fun v : V => (v : ι → ℝ)) hy0 hy1
        (fun v => Finset.mem_coe.mpr v.2) hx
  rw [hull]
  refine exists_congr fun y => ?_
  have r0 : (polyA ι *ᵥ x + polyB V *ᵥ y) none = ∑ v, y v := by
    rw [Pi.add_apply, mv, mv]
    simp [polyA, polyB]
  have r1 : ∀ i, (polyA ι *ᵥ x + polyB V *ᵥ y) (some i) = x i - ∑ v, y v * (v : ι → ℝ) i := by
    intro i
    rw [Pi.add_apply, mv, mv]
    have e1 : ∑ j, polyA ι (some i) j * x j = x i := by simp [polyA]
    have e2 : ∑ v, polyB V (some i) v * y v = -∑ v, y v * (v : ι → ℝ) i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      simp only [polyB, Matrix.of_apply, Option.elim_some]
      ring
    rw [e1, e2]
    ring
  have hle : (0 : Matrix V ι ℝ) *ᵥ x + (-1 : Matrix V V ℝ) *ᵥ y ≤ 0 ↔ ∀ v, 0 ≤ y v := by
    rw [Matrix.zero_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, zero_add, neg_nonpos]
    exact Pi.le_def
  have ha0 : polya ι none = 1 := rfl
  have ha1 : ∀ i, polya ι (some i) = 0 := fun i => rfl
  simp only [hle, funext_iff, Option.forall, r0, r1, ha0, ha1, sub_eq_zero]
  constructor
  · rintro ⟨h3, h1, h2⟩
    exact ⟨⟨h1, fun i => (h2 i).symm⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, h1, fun i => (h2 i).symm⟩

/-! ### Minkowski sum -/

def bigA {ι S₁ S₂ : Type*} (A₂ : Matrix S₂ ι ℝ) : Matrix (S₁ ⊕ S₂) ι ℝ :=
  Matrix.of fun s i => Sum.elim (fun _ => 0) (fun s₂ => A₂ s₂ i) s

def bigB {ι S₁ S₂ T₁ T₂ : Type*} (A₁ : Matrix S₁ ι ℝ) (B₁ : Matrix S₁ T₁ ℝ)
    (A₂ : Matrix S₂ ι ℝ) (B₂ : Matrix S₂ T₂ ℝ) : Matrix (S₁ ⊕ S₂) (ι ⊕ (T₁ ⊕ T₂)) ℝ :=
  Matrix.of fun s k => Sum.elim
    (fun s₁ => Sum.elim (fun i => A₁ s₁ i) (Sum.elim (fun j => B₁ s₁ j) (fun _ => 0)) k)
    (fun s₂ => Sum.elim (fun i => -A₂ s₂ i) (Sum.elim (fun _ => 0) (fun j => B₂ s₂ j)) k) s

lemma rows {ι S₁ S₂ T₁ T₂ : Type*} [Fintype ι] [Fintype T₁] [Fintype T₂]
    (A₁ : Matrix S₁ ι ℝ) (B₁ : Matrix S₁ T₁ ℝ)
    (A₂ : Matrix S₂ ι ℝ) (B₂ : Matrix S₂ T₂ ℝ) (x : ι → ℝ) (y : ι ⊕ (T₁ ⊕ T₂) → ℝ) :
    bigA (S₁ := S₁) A₂ *ᵥ x + bigB A₁ B₁ A₂ B₂ *ᵥ y =
      Sum.elim (A₁ *ᵥ (fun i => y (Sum.inl i)) + B₁ *ᵥ (fun j => y (Sum.inr (Sum.inl j))))
        (A₂ *ᵥ (x - fun i => y (Sum.inl i)) + B₂ *ᵥ (fun j => y (Sum.inr (Sum.inr j)))) := by
  funext s
  cases s with
  | inl s =>
    simp only [Pi.add_apply, mv, bigA, bigB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, zero_add] <;> ring
  | inr s =>
    simp only [Pi.add_apply, Pi.sub_apply, mv, bigA, bigB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul,
      Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib] <;> ring

lemma elim_eq_iff {S₁ S₂ : Type*} (u₁ g₁ : S₁ → ℝ) (u₂ g₂ : S₂ → ℝ) :
    Sum.elim u₁ u₂ = Sum.elim g₁ g₂ ↔ u₁ = g₁ ∧ u₂ = g₂ := by
  constructor
  · intro h
    exact ⟨funext fun s => congrFun h (Sum.inl s), funext fun s => congrFun h (Sum.inr s)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma elim_le_iff {S₁ S₂ : Type*} (u₁ g₁ : S₁ → ℝ) (u₂ g₂ : S₂ → ℝ) :
    Sum.elim u₁ u₂ ≤ Sum.elim g₁ g₂ ↔ u₁ ≤ g₁ ∧ u₂ ≤ g₂ := by
  constructor
  · intro h
    exact ⟨Pi.le_def.mpr fun s => Pi.le_def.mp h (Sum.inl s),
      Pi.le_def.mpr fun s => Pi.le_def.mp h (Sum.inr s)⟩
  · rintro ⟨h1, h2⟩
    refine Pi.le_def.mpr fun s => ?_
    cases s with
    | inl s => exact Pi.le_def.mp h1 s
    | inr s => exact Pi.le_def.mp h2 s

lemma sumEF {ι : Type*} [Fintype ι] (P₁ P₂ : Set (ι → ℝ)) (r₁ r₂ : ℕ)
    (h1 : IsEFOfSize P₁ r₁) (h2 : IsEFOfSize P₂ r₂) : IsEFOfSize (P₁ + P₂) (r₁ + r₂) := by
  classical
  obtain ⟨k₁, p₁, A₁, B₁, a₁, C₁, D₁, d₁, hP₁⟩ := h1
  obtain ⟨k₂, p₂, A₂, B₂, a₂, C₂, D₂, d₂, hP₂⟩ := h2
  refine toEF (P₁ + P₂) (r₁ + r₂) finSumFinEquiv (bigA (S₁ := Fin p₁) A₂) (bigB A₁ B₁ A₂ B₂)
    (Sum.elim a₁ a₂) (bigA (S₁ := Fin r₁) C₂) (bigB C₁ D₁ C₂ D₂) (Sum.elim d₁ d₂) ?_
  intro x
  rw [Set.mem_add]
  constructor
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    obtain ⟨y₁, e₁, l₁⟩ := (hP₁ x₁).mp hx₁
    obtain ⟨y₂, e₂, l₂⟩ := (hP₂ x₂).mp hx₂
    refine ⟨Sum.elim x₁ (Sum.elim y₁ y₂), ?_, ?_⟩
    · rw [rows, elim_eq_iff]
      have hx : (x₁ + x₂ - fun i => Sum.elim x₁ (Sum.elim y₁ y₂) (Sum.inl i)) = x₂ := by
        funext i; simp
      rw [hx]
      exact ⟨e₁, e₂⟩
    · rw [rows, elim_le_iff]
      have hx : (x₁ + x₂ - fun i => Sum.elim x₁ (Sum.elim y₁ y₂) (Sum.inl i)) = x₂ := by
        funext i; simp
      rw [hx]
      exact ⟨l₁, l₂⟩
  · rintro ⟨y, he, hl⟩
    rw [rows, elim_eq_iff] at he
    rw [rows, elim_le_iff] at hl
    refine ⟨fun i => y (Sum.inl i), (hP₁ _).mpr ⟨_, he.1, hl.1⟩,
      x - fun i => y (Sum.inl i), (hP₂ _).mpr ⟨_, he.2, hl.2⟩, ?_⟩
    funext i
    simp

end Aux_PSDPolyApprox_xc_minkowski_sum

open Aux_PSDPolyApprox_xc_minkowski_sum in
theorem solution {ι : Type*} [Fintype ι] (P₁ P₂ : Set (ι → ℝ))
    (h₁ : IsPolytope P₁) (h₂ : IsPolytope P₂) :
    extensionComplexity (P₁ + P₂) ≤ extensionComplexity P₁ + extensionComplexity P₂ := by
  obtain ⟨r₁, hr₁⟩ := polyEF P₁ h₁
  obtain ⟨r₂, hr₂⟩ := polyEF P₂ h₂
  have m1 : IsEFOfSize P₁ (extensionComplexity P₁) :=
    Nat.sInf_mem (s := {r : ℕ | IsEFOfSize P₁ r}) ⟨r₁, hr₁⟩
  have m2 : IsEFOfSize P₂ (extensionComplexity P₂) :=
    Nat.sInf_mem (s := {r : ℕ | IsEFOfSize P₂ r}) ⟨r₂, hr₂⟩
  show sInf {r : ℕ | IsEFOfSize (P₁ + P₂) r} ≤ _
  exact Nat.sInf_le (sumEF P₁ P₂ _ _ m1 m2)
